# Codex integration

This directory is an adapter layer; the MCP server itself is client-neutral.

## Boundary

| Concern | Codex implementation | Shared/Claude implementation |
|---|---|---|
| Package discovery | `.codex-plugin/plugin.json` | unchanged |
| MCP launch | inline `mcpServers.hol4` manifest entry | server process and tools |
| Proof workflow | bundled `skills/hol4-proving/` | canonical skill content |
| Lifecycle registration | `hooks/hooks.json` | `h*.py` policy scripts |
| Edit payload | temporary `apply_patch` preview | Edit-style before/after checks |
| User consent history | stable `UserPromptSubmit.prompt` capture | transcript-reading helpers |
| Writable state | `PLUGIN_DATA/runtime-home` | path conventions only |

- `hook_adapter.py` translates Codex `apply_patch` events into before/after
  edit payloads understood by the established HOL4 policy scripts.
- `prompt_capture.py` records the stable `UserPromptSubmit.prompt` field so
  consent-aware policies do not depend on Codex's intentionally unstable
  transcript format.
- `session_context.py` asks Codex to load the bundled `hol4-proving` skill when
  a session starts in a HOL4 project.

Codex supplies `PLUGIN_ROOT` and `PLUGIN_DATA`. The adapter runs existing hook
scripts with `HOME=$PLUGIN_DATA/runtime-home`; consequently their legacy
`~/.claude/hook-state` paths resolve inside plugin-owned Codex data. Nothing in
this integration reads or writes the user's actual Claude configuration or
hook state.

`hooks/hooks.json` is the native Codex lifecycle configuration. H14 is omitted
because it is a general, user-specific Git policy rather than HOL4 policy. H22
is replaced by the Codex-native session hook because its other responsibility
is auditing Claude's `settings.json` wiring.

## Event flow

1. `UserPromptSubmit` records bounded prompt history under `PLUGIN_DATA`.
2. `PreToolUse` passes Bash and HOL4 MCP arguments through unchanged. For
   `apply_patch`, the adapter materializes only referenced files in a temporary
   directory and derives an Edit payload without touching the working tree.
3. The selected `h*.py` policies run sequentially with an isolated HOME. Exit
   code 2 and stderr remain a hard block; advisory JSON is combined into one
   Codex-compatible response.
4. `PostToolUse` forwards `tool_response`, allowing the existing replay,
   failure, build, and proof-sweep advisories to work unchanged.

The adapter fails open on malformed or unsupported hook input, matching the
existing suite's policy. When possible, it surfaces an explicit Codex warning
instead of silently losing coverage.
