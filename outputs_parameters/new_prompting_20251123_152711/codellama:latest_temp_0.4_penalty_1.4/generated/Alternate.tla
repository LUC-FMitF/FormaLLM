---- MODULE Alternate ----
-------------------------------MODULE AlternatingActions-----------------------
(*****************************************************************************)
(* This specifies a system that alternately performs two actions, which    *)
* for now I will call A_0 and A_1.  It uses a variable v whose value      *)
* alternates between 0 and 1, performing an A_0 action when v changes     *)
* from 0 to 1, and an A_1 action when v changes from 1 to 0.              *)
(*****************************************************************************)
CONSTANTS   XInit,    \* The initial state predicate for x.
            XAct      \* An operator that asserts the actions of a system.
VARIABLES   v         \* The variable representing which action is taken.
INITIAL     v = 0                              \* Initialize to A_0.
TRANSITION  (v'=1-v) /\ XAct(v, v', v')        \* Alternate between actions.
NEXT        [][Next]_<<v>>
------------------------------------------------------------------------------
Spec ==    \EE v : Spec                         \* The specification for the system.
=============================================================================
TLC CONFIGURATION:
CONSTANTS   XInit,       \* Initial state predicate.
            XAct        \* Action operator.
VARIABLES   v           \* Variable representing which action is taken.
INITIAL     v = 0                              \* Initialize to A_0.
TRANSITION  (v'=1-v) /\ XAct(v, v', v')        \* Alternate between actions.
NEXT        [][Next]_<<v>>
=============================================================================