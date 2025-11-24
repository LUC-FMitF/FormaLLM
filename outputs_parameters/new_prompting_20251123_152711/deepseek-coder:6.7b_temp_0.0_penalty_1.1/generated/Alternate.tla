---- MODULE Alternate ----

(***************************************************************************************)
(* This specifies a system that alternately performs two actions, which we will call   *)
(* A_0 and A_1. It uses a variable v whose value alternates between 0 and 1, performing *)
(* an A_0 action when v changes from 0 to 1, and an A_1 action when v changes from 1 to 0.*)
(***************************************************************************************)

CONSTANTS   XInit,           \* Constant operator for initial value of x.
            XAct             \* Constant operator for actions on x.
VARIABLES   v,               \* Variable representing the state of the system.
            x                \* Part of the state that is changed by A_0 and A_1 actions.
----------------------------------------------------------------------------------------
Spec == [XInit(x)] /\ (v' = 1 - v) /\ XAct(v, x, x')  \* Specification for AlternatingActions.

(* TLC Configuration *)
CONSTANTS   XInit = <lambda> x : TRUE,    \* Assume that x has a correct initial value.
            XAct  = <lambda> i, xInit, xNext : (i = 0 /\ x' = xNext) \/ (i = 1 /\ x' = xNext)  \* Assume that changing the value of x from xInit to xNext represents an A_i action.
=============================================================================================
====
(* Theorems *)
THEOREM    Spec => []Spec   (* Initial state is a valid state according to the specification. *)
=============================================================================================
====
*********************************************************************************************
*** This TLA+ module specifies an alternating actions system with two actions A_0 and A_1,*)
*** where x represents the part of the state that changes due to these actions. The variable v*)
*** alternates between 0 and 1, performing an A_0 action when it changes from 0 to 1, and an *)
*** A_1 action when it changes from 1 to 0. The TLC configuration specifies the initial value*)
*** of x (XInit) and the actions on x (XAct).                                               *)
*********************************************************************************************
*)
====