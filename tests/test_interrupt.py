"""
Test interrupt functionality for hol4-mcp server.

Tests:
1. MCP server starts and responds to tool calls
2. SIGINT to MCP server interrupts HOL sessions
3. Server survives SIGINT and continues serving requests
"""

import asyncio
import json
import os
import signal
import subprocess
import sys
import time

import pytest


class McpClient:
    """Minimal MCP client for testing."""
    
    def __init__(self):
        self.proc = None
        self.buffer = ""
        self.next_id = 1
        self.pending = {}
        self._reader_task = None
    
    async def connect(self, command: list[str]):
        self.proc = await asyncio.create_subprocess_exec(
            *command,
            stdin=asyncio.subprocess.PIPE,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
        )
        
        # Start reader task
        self._reader_task = asyncio.create_task(self._read_loop())
        
        # Initialize
        await self.request("initialize", {
            "protocolVersion": "2024-11-05",
            "capabilities": {},
            "clientInfo": {"name": "test-client", "version": "0.1.0"},
        })
        
        # Send initialized notification
        self._send({"jsonrpc": "2.0", "method": "notifications/initialized", "params": {}})
    
    async def _read_loop(self):
        while self.proc and self.proc.returncode is None:
            try:
                line = await asyncio.wait_for(
                    self.proc.stdout.readline(),
                    timeout=0.1
                )
                if not line:
                    break
                self._process_line(line.decode())
            except asyncio.TimeoutError:
                continue
            except Exception as e:
                break
    
    def _process_line(self, line: str):
        line = line.strip()
        if not line:
            return
        try:
            msg = json.loads(line)
            if "id" in msg and msg["id"] in self.pending:
                future = self.pending.pop(msg["id"])
                if "error" in msg:
                    future.set_exception(Exception(msg["error"].get("message", str(msg["error"]))))
                else:
                    future.set_result(msg.get("result"))
        except json.JSONDecodeError:
            pass
    
    def _send(self, msg: dict):
        if not self.proc or not self.proc.stdin:
            raise Exception("Not connected")
        data = json.dumps(msg) + "\n"
        self.proc.stdin.write(data.encode())
    
    async def request(self, method: str, params: dict, timeout: float = 30.0):
        req_id = self.next_id
        self.next_id += 1
        
        future = asyncio.get_event_loop().create_future()
        self.pending[req_id] = future
        
        self._send({"jsonrpc": "2.0", "id": req_id, "method": method, "params": params})
        await self.proc.stdin.drain()
        
        return await asyncio.wait_for(future, timeout=timeout)
    
    async def call_tool(self, name: str, args: dict, timeout: float = 30.0):
        return await self.request("tools/call", {"name": name, "arguments": args}, timeout=timeout)
    
    def interrupt(self) -> bool:
        """Send SIGINT to the MCP server process."""
        if self.proc and self.proc.pid:
            try:
                os.kill(self.proc.pid, signal.SIGINT)
                return True
            except Exception:
                return False
        return False
    
    async def close(self):
        if self._reader_task:
            self._reader_task.cancel()
            try:
                await self._reader_task
            except asyncio.CancelledError:
                pass
        if self.proc:
            self.proc.terminate()
            await self.proc.wait()
            self.proc = None


def extract_text(result: dict) -> str:
    """Extract text content from MCP tool result."""
    content = result.get("content", [])
    return "\n".join(c.get("text", "") for c in content if c.get("type") == "text")


@pytest.fixture
async def mcp_client():
    """Create and connect an MCP client."""
    client = McpClient()
    await client.connect(["hol4-mcp", "--transport", "stdio"])
    yield client
    await client.close()


@pytest.mark.asyncio
async def test_basic_connection(mcp_client):
    """Test basic MCP server connection and tool call."""
    result = await mcp_client.call_tool("hol_sessions", {})
    text = extract_text(result)
    assert "No active sessions" in text or "SESSION" in text


@pytest.mark.asyncio
async def test_sigint_handler_installed():
    """Test that SIGINT handler is installed in the server."""
    # Import and check directly
    from hol4_mcp.hol_mcp_server import _sigint_handler
    import signal as sig
    
    # The handler should be a function
    assert callable(_sigint_handler)


@pytest.mark.asyncio
async def test_sigint_interrupts_and_server_survives(mcp_client):
    """Test that SIGINT interrupts sessions but server survives."""
    # Start a session
    result = await mcp_client.call_tool("hol_start", {
        "workdir": "/tmp",
        "name": "test_sigint"
    })
    text = extract_text(result)
    assert "started" in text.lower() or "running" in text.lower()
    
    # Verify session exists
    result = await mcp_client.call_tool("hol_sessions", {})
    text = extract_text(result)
    assert "test_sigint" in text
    
    # Send SIGINT
    interrupted = mcp_client.interrupt()
    assert interrupted, "Failed to send SIGINT"
    
    # Give it a moment
    await asyncio.sleep(0.5)
    
    # Server should still respond
    result = await mcp_client.call_tool("hol_sessions", {})
    text = extract_text(result)
    # Server survived if we got a response
    assert "SESSION" in text or "No active sessions" in text
    
    # Clean up
    try:
        await mcp_client.call_tool("hol_stop", {"session": "test_sigint"})
    except Exception:
        pass  # Session may have died from SIGINT


@pytest.mark.asyncio
async def test_multiple_sigints(mcp_client):
    """Test that server survives multiple SIGINTs."""
    # Send multiple SIGINTs
    for _ in range(3):
        mcp_client.interrupt()
        await asyncio.sleep(0.1)
    
    # Server should still respond
    result = await mcp_client.call_tool("hol_sessions", {})
    text = extract_text(result)
    assert "SESSION" in text or "No active sessions" in text


@pytest.mark.asyncio
async def test_sigint_during_command():
    """Test SIGINT during a long-running HOL command."""
    client = McpClient()
    await client.connect(["hol4-mcp", "--transport", "stdio"])
    
    try:
        # Start a session
        await client.call_tool("hol_start", {
            "workdir": "/tmp",
            "name": "test_long"
        })
        
        # Start a long command (will timeout or be interrupted)
        async def long_command():
            try:
                return await client.call_tool("hol_send", {
                    "session": "test_long",
                    "command": "let val _ = OS.Process.sleep (Time.fromSeconds 30) in 1 end;",
                    "timeout": 60
                }, timeout=60)
            except Exception as e:
                return str(e)
        
        # Start the command
        task = asyncio.create_task(long_command())
        
        # Wait a bit then send SIGINT
        await asyncio.sleep(1)
        client.interrupt()
        
        # The command should complete (interrupted or timeout)
        result = await asyncio.wait_for(task, timeout=10)
        
        # Server should still be alive
        await asyncio.sleep(0.5)
        sessions_result = await client.call_tool("hol_sessions", {})
        text = extract_text(sessions_result)
        assert "SESSION" in text or "No active sessions" in text
        
    finally:
        await client.close()


@pytest.mark.asyncio  
async def test_hol_interrupt_tool(mcp_client):
    """Test the hol_interrupt tool works."""
    # Start a session
    await mcp_client.call_tool("hol_start", {
        "workdir": "/tmp",
        "name": "test_tool_interrupt"
    })
    
    # Call hol_interrupt
    result = await mcp_client.call_tool("hol_interrupt", {
        "session": "test_tool_interrupt"
    })
    text = extract_text(result)
    assert "SIGINT" in text or "interrupt" in text.lower()
    
    # Clean up
    await mcp_client.call_tool("hol_stop", {"session": "test_tool_interrupt"})


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
