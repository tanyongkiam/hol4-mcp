open HolKernel Parse boolLib bossLib markerLib;

val _ = new_theory "suspend";

Theorem split_conj:
  p /\ (p ==> q) ==> p /\ q
Proof
  strip_tac >> conj_tac
  >- suspend "p_case"
  >- suspend "q_case"
QED

Resume split_conj[p_case]:
  ASM_REWRITE_TAC[]
QED

Resume split_conj[q_case]:
  RES_TAC
QED

Finalise split_conj

Theorem simple_suspend:
  p /\ q ==> q /\ p
Proof
  rpt strip_tac >> suspend "swap"
QED

Resume simple_suspend[swap]:
  RESUME_TAC >> FIRST_ASSUM ACCEPT_TAC
QED

Finalise simple_suspend

val _ = export_theory();
