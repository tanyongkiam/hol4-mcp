Suspected: local-block discovery still mistakes SML lexical constructs.

The scanner tracks `local` and `let`, but not `struct`/`sig`/`abstype` despite
their matching `end`. Nested local blocks are returned in closing order, so
cursor lookup may choose an inner block when HOL needs the outer declaration.
Comment stripping also runs before string stripping; a literal `"(*"` may
hide the remainder of the script. Expected: preserve the correct outer local
span and real keywords after strings. These are source-level suspicions;
minimal parser tests and live HOL confirmation are still needed.
