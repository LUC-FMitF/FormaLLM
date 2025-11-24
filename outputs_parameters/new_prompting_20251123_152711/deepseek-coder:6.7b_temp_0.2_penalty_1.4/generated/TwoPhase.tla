---- MODULE TwoPhase ----

(***************************************************************************)
(* This module specifies the two-phase handshake, which is a simple but     *)
(* very important hardware protocol by which a Producer process and a       *)
(* Consumer process alternately perform actions, with the Producer going    *)
(* first.  The system is pictured as follows:                               *)
*)
`.                                                                       *)
------------           p          ------------                       *)
|            | -----------------> |            |                      *)
| Producer  |                    |  Consumer  |  .                    *)
|            |<------------------ |            |                      *)
------------          c            -------    .'                 *)
*)
(* In the spec, we represent the Producer and Consumer actions the way we  *)
(* represented the actions A_0 and A_1 of the Alternate specification. We   *)
(* then show that this specification implements the Alternate               *)
(* specification under a suitable refinement mapping (substitution for the  *)
(* variable v).                                                             *)
***************************************************************************)

LOCAL INSTANCE RMConstants = {r1, r2, r3} (* Refinements *)

\* The invariant that is needed for the proof.                       *)
TPInv == [](p /\ ~c) \/ (~p /\ c)  -- "Two-phase handshake protocol"

(* We prove that specification TPSpec implement(s) the specification   *)
(* obtained by substiting a state function vBar for the variable v, where*)
(* vBar is defined as follows.                                              *)
***************************************************************************)
\* The following statement imports, for every defined operator D of module  *)
(* Alternate, a definition of A\!D to equal the definition of D with vBar    *)
(* substituted for v and with the parameters x, XInit, and XAct of this     *)
(* module substituted for the parameters of the same name of module         *)
(* Alternate.  Thus, A\!Spec is defined to be the formula Spec of module   *)
(* Alternate with vBar substituted for v.                                   *)
***************************************************************************)
\* The following theorem is a standard proof that one specification        *)
(* implements (the safety part of) another specification under a            *)
(* refinement mapping.  In fact, the temporal leaf proofs will be exactly   *)
(* the same one-liners for every such proof.  In realistic example, the     *)
(* non-temporal leaf proofs will be replaced by fairly long structured      *)
(* proofs--especially the two substeps numbered <2>2.                       *)
***************************************************************************)
\* The specification TPSpec is implemented under refinement mapping RM    *)
TPSpecImplemented == [](p /\ ~c) \/ (~p /\ c)  -- "Two-phase handshake protocol"
SPECIFICATION TPTypeOK => []TPInv/\[](XInit[RM]_<==> XAct[RM])_U_(<>)_<<TPImplemented
=====