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
| Producer  |                    | Consumer  |                      *)
|            | <----------------- |            |                      *)
------------           c          ------------    .'                *)
*)
*)
(* In the spec, we represent the Producer and Consumer actions the way we   *)
(* represent actions A_0 and A_1 of the Alternate specification.  We  *)
(* then show that this specification implements the Alternate               *)
(* specification under a suitable refinement mapping (substitution for the  *)
(* variable v).                                                             *)
***************************************************************************)
***************************************************************************)
INVARIANT Inv
SPECIFICATION Spec
=============================================================================
====



(***************************************************************************)
(* We prove that specification Spec implement (implies) the specification   *)
(* obtained by substiting a state function vBar for the variable v, where   *)
(* vBar is defined as follows.                                              *)
***************************************************************************)
***************************************************************************)
THEOREM TPImplements 
    ==> ([x \in RM |-> <x>_0 in Spec] /\ [x \in RM |-> <x>_1 in Spec])
=============================================================================
====