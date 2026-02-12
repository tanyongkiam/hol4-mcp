(*
  Test script with multi-tactic termination proof.
*)

open HolKernel Parse boolLib bossLib;

val _ = new_theory "defn2";

(* Definition with multi-step termination proof *)
Definition collatz_steps_def:
  collatz_steps (n:num) (fuel:num) =
    if fuel = 0 then fuel
    else if n <= 1 then 0
    else if EVEN n then collatz_steps (n DIV 2) (fuel - 1)
    else collatz_steps (3 * n + 1) (fuel - 1)
Termination
  WF_REL_TAC `measure (SND)` >>
  simp[]
End

(* Theorem referencing the definition *)
Theorem collatz_steps_0:
  !n. collatz_steps n 0 = 0
Proof
  simp[Once collatz_steps_def]
QED

val _ = export_theory();
