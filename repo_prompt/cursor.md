# Proof Cursor Recovery Prompt

## Files: `hol_cursor.py`, `hol_file_parser.py`

File-based proof development: parse SML, track position, splice completed proofs.

## TheoremInfo Dataclass

```python
@dataclass
class TheoremInfo:
    name: str                    # Theorem name
    kind: str                    # "Theorem", "Triviality", "Definition"
    goal: str                    # The goal term (backquoted)
    start_line: int              # Line number in file
    proof_start_line: int        # Line of "Proof"
    proof_end_line: int          # Line of "QED"
    has_cheat: bool              # Contains cheat in proof
    proof_body: str = ""         # Content between Proof and QED
    attributes: list[str] = []   # e.g. ["simp", "local"]
```

## File Parser

```python
def parse_theorems(content: str) -> list[TheoremInfo]:
    """Parse SML file for theorem blocks.

    Recognizes:
    - Theorem name: goal Proof tactics QED
    - Triviality name: goal Proof tactics QED
    - Definition name = term

    Extracts goal from backquotes, identifies cheat locations.
    """

def splice_into_theorem(content: str, name: str, new_tactics: str) -> str:
    """Replace proof body of named theorem.

    Finds: Theorem name: ... Proof OLD QED
    Replaces with: Theorem name: ... Proof NEW QED

    Preserves formatting, handles multi-line proofs.
    """

def parse_p_output(output: str) -> str:
    """Extract tactic script from p() output.

    p() prints the recorded proof tree. This function extracts
    just the tactic script suitable for splicing into file.
    """
```

## ProofCursor Class

```python
class ProofCursor:
    file_path: Path
    theorems: list[TheoremInfo]
    current_index: int
    completed: list[str]  # Names of completed theorems

    def __init__(self, file_path: Path):
        """Parse file, find theorems with cheats."""

    def initialize(self, session: HOLSession) -> str:
        """Set up HOL context for proving.

        1. Parse file for theorems
        2. Find first theorem with cheat
        3. Load file content up to that theorem into HOL
           (so dependencies are available)
        4. Enter goaltree for first cheat
        5. Return top_goals()
        """

    def start_current(self, session: HOLSession) -> str:
        """Enter goaltree for current theorem.

        1. gt `goal`
        2. Use TacticParse (via extract_before_cheat SML helper) to find
           pre-cheat tactics, preserving original structure (>-, >>, \\)
        3. Replay as single etq call (not split into parts)
        4. Return status
        """

    def complete_and_advance(self, session: HOLSession) -> dict:
        """Extract proof, drop goal, advance to next cheat.

        Call when proof is done (no goals left). Returns dict with:
        - proof: tactic script from p()
        - theorem: name of completed theorem
        - next_cheat: {name, line} or None

        Agent must splice proof into file, then call reenter() to
        set up goaltree for the next theorem.
        """

    def reenter(self, session: HOLSession) -> str:
        """Set up goaltree for current theorem.

        Drops ALL goaltrees (clears any stacked), enters goaltree.
        Use after complete_and_advance to start next theorem, or to
        retry a proof from scratch.
        """

    @property
    def status(self) -> dict:
        """Return progress info: file, position, current, remaining."""
```

## Workflow

```
cursor_init(file)
    │
    ▼
┌─────────────────┐
│ Parse file      │
│ Find cheats     │
│ Load context    │
│ Enter goaltree  │
└────────┬────────┘
         │
         ▼
┌─────────────────┐     ┌─────────────────┐
│ Prove with etq  │────▶│ cursor_complete │
│ backup() if bad │     │ (calls p()      │
│ until no goals  │     │  splices file)  │
└─────────────────┘     └────────┬────────┘
         ▲                       │
         │                       │
         └───────────────────────┘
                  (repeat)
```

## Context Loading

When entering a theorem mid-file, previous definitions must be loaded:

```sml
(* File content up to current theorem is sent to HOL *)
(* This makes prior Theorems/Definitions available *)
```

The cursor tracks what's been loaded to avoid re-loading.

## Reconstruction Notes

- Parsing uses regex for Theorem/Triviality/Definition blocks
- Cheat detection looks for literal `cheat` in proof body
- Pre-cheat extraction uses TacticParse (SML) to correctly find cheat in AST
  - Preserves original tactic structure (>-, >>, \\)
  - See hol4_mcp/sml_helpers/cheat_finder.sml
- Splicing preserves indentation and file structure
- p() output format depends on etq.sml implementation
