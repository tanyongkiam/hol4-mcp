Suspected: Codex patch previews lose coverage for absolute paths and renames.

Source inspection: `hook_adapter._safe_relative` rejects absolute paths;
`preview_patch` and its fallback attribute moved content only to the source
path. A move from a plain file to `*Script.sml` could skip proof policy checks.
Expected: inspect the actual destination content without modifying real files.
Observed so far: these branches are visible in the adapter; regression tests
for absolute paths and moves are still needed. Existing tests cover relative
updates/additions only. Also check fallback handling of anchors and end-of-file
insertions before trusting its generated before/after content.
