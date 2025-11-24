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
|            |<------------------ |            |  ^                  *)
------------          c            -------      ---'                 *)
*)
(* In the spec, we represent the Producer and Consumer actions the way we  *)
(* represented the actions A_0 and A_1 of the Alternate specification. We then show that this *)
(* specification implements the Alternate specification under a suitable refinement mapping (substitution for the variable v).*)
***************************************************************************)

LOCAL INSTANCE RMConstants = {r1, r2, r3} (* Refinements *)

\* The state function representing our protocol.  It is parameterized by two sets: XInit and XAct which represent respectively the initial states of both processes (Producer & Consumer)*)
LOCAL FUNCTION v(x : RMConstants)(XInit, XAct) == ... (* Define your invariant here *)

\* The specification for our protocol.  It is parameterized by two sets: XInit and XAct which represent respectively the initial states of both processes (Producer & Consumer).*)
LOCAL SPECIFICATION TPSpec(x : RMConstants)(XInit, XAct) == ... (* Define your specification here *)

\* The invariant for our protocol.  It is parameterized by two sets: XInit and XAct which represent respectively the initial states of both processes (Producer & Consumer).*)
LOCAL INVARIANT TPTypeOK(x : RMConstants)(XInit, XAct) == ... (* Define your invariant here *)

\* The theorem that shows our protocol is correct.  It is parameterized by two sets: XInit and XAct which represent respectively the initial states of both processes (Producer & Consumer).*)
LOCAL THEOREM TPProof(x : RMConstants)(XInit, XAct) == ... (* Define your proof here *)
=============================================================================
====