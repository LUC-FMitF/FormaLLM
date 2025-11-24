---- MODULE TwoPhase ----

(***************************************************************************)
(* This module specifies the two-phase handshake, which is a simple but     *)
(* very important hardware protocol by which a Producer process and a       *)
(* Consumer process alternately perform actions, with the Producer going    *)
(* first.  The system is pictured as follows:                               *)
*)
(* `.                                                                       *)
------------           p          ------------                       *)
|            | -----------------> |            |                      *)
| Producer  |                    | Consumer  |                      *)
|            | <----------------- |            |                      *)
------------           c          ------------    .'                 *)
*)
(* In the spec, we represent the Producer and Consumer actions the way we   *)
(* represent actions A_0 and A_1 of the Alternate specification.  We then show that this *)
(* specification implements the Alternate specification under a suitable refinement mapping *)
(* (substitution for the variable v).                                                             *)
***************************************************************************)

(***************************************************************************)
(* Specification of Alternate protocol.                                          *)
*)
... (* This is where you define your operators and invariants for the Alternate module *)

=============================================================================
====



(***************************************************************************)
(* Definition of vBar as a state function.                                   *)
*)
... (* Define your vBar here *)

\* Import operators from the Alternate module, substituting in our definition of vBar. *)
FORALL (D \in OPERATORS(Alternate)): A\!D == D[vBar] /\ XInit == Alternate.XInit[vBar] /\ XAct == Alternate.XAct[vBar]

(* Specification of TwoPhaseHandshake protocol, implemented under the substitution for v *)
TPSpec == ... (* Define your specification here using operators from Alternate module and vBar *)

INVARIANT TPTypeOK == 
  (* Add your type invariant here *)

SPECIFICATION TPSpec AND Inv[vBar]

(* Proof that TwoPhaseHandshake protocol implements the Alternate protocol under a refinement mapping. *)
THEOREM ([]Spec_implements_Alternate)[RM] == Spec_implements(TwoPhaseHandshake, Alternate)
=============================================================================
====