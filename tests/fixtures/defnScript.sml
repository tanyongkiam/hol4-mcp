(*
  Test script with Definition ... Termination ... End block.
  Tests recursive function definition with explicit termination proof.
*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "defn";

(* Simple recursive definition with Termination block *)
Definition fact_def:
  fact (n:num) = if n = 0 then 1 else n * fact (n - 1)
Termination
  WF_REL_TAC `measure I`
End

(* Theorem using the definition *)
Theorem fact_0:
  fact 0 = 1
Proof
  simp[Once fact_def]
QED

val _ = export_theory();
