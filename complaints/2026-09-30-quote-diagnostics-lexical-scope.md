Suspected: smart-quote diagnosis includes valid comment/string contents.

`quote_check.find_unmatched_quotes` scans every character, including SML
comments and strings. `quote_diagnosis_lines` can consequently blame a quote
inside a valid comment/string for an unrelated parse error; the recommended
`--fix` changes that content too. Example candidate: `(* author's note: ’ *)`
followed by otherwise valid SML. An unmatched quote there is ordinary comment
text, not a HOL quotation delimiter.

Verify both the standalone utility's intended scope and MCP error diagnosis
with lexical controls before changing it. No runtime reproducer is saved yet.
