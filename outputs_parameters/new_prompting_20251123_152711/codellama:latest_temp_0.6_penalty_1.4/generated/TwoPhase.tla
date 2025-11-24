---- MODULE TwoPhase ----

(**************************************************************************)
(* Generated at Sat Oct 31 03:15:55 PDT 2009                              *)
(**************************************************************************)
CONSTANTS   RM,        \* The set of all roles.
            A_0,       \* The Producer action.
            A_1,       \* The Consumer action.
            XInit,    \* The initial state function.
            XAct      \* The transition relation.
INVARIANT  Inv,     \* The invariant that is needed for the proof.
SPECIFICATION Spec
====