---- MODULE Alternate ----

(***************************************************************************************)
(* This specifies a system that alternately performs two actions, which we will call A_0 *)
(* and A_1. It uses a variable v whose value alternates between 0 and 1, performing an   *)
(* A_0 action when v changes from 0 to 1, and an A_1 action when v changes from 1 to 0. *)
(* We let the variable x to represent the part of the state that is changed by the A_0  *)
(* and A_1 actions. We introduce two constant operators XInit and XAct, where XInit(x)   *)
(* is assumed to assert that x has a correct initial value, and XAct(i, xInit, xNext)   *)
(* is assumed to assert that changing the value of x from xInit to xNext represents an*)
(* A_i action, for i=0, 1.                                                            *)
(* We hide v in the specification Spec with v hidden. Engineers are interested in what*)
(* works, not what is philosophically correct, so we don't worry about this.             *)
(***************************************************************************************)

CONSTANTS
    A_0 = "Action 0"
    A_1 = "Action 1"
    
VARIABLES
    v, x \in {A_0, A_1}

ASSUME
    XInit(x) == True /\ (v = 0 => AFTER[{v'}] x' = A_0) /\ (v = 1 => AFTER[{v'}] x' = A_1)
    
PROCEDURE NextState() ==
    CASE v = 0 -> [x ](A_1) // A_0 action
        [] v = 1 -> [x ](A_0) // A_1 action
        [] OTHER -> [x ](v)

SPECIFICATION Spec == ([][NextState]_<<x>> /\ XInit(x)) => AFTER[{v}] True

TLC Configuration:
CONSTANTS
    Actions = {A_0, A_1}

=============================================================================
====