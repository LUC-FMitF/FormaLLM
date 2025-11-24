---- MODULE Alternate ----

(***************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009                               *)
(***************************************************************************)
CONSTANTS   v,            \* The variable representing the part of the state that is changed by the A_0 and A_1 actions.
            XInit,        \* The constant operator used to assert that x has a correct initial value.
            XAct          \* The constant operator used to assert that changing the value of x from xInit to xNext represents an A_i action, for i=0, 1.
VARIABLES   x             \* The part of the state changed by the A_0 and A_1 actions.
            xInit         \* The initial value of x.
            xNext         \* The next value of x after an A_i action has been performed, for i=0, 1.
------------------------------------------------------------------------------
Spec ==                   \* The specification that alternately performs two actions, which we will call A_0 and A_1.
    /\ v = [x |-> XInit(x)]        \* We let the variable x to represent the part of the state changed by the A_0 and A_1 actions.
    /\ \A i : 0..1 =>                   \* For all values of i, either an A_i action has been performed or it is not known whether one was performed.
        (v = [x |-> XAct(i, xInit, xNext)] <=> v'[x] = XAct(i, xInit, xNext)) \* If the value of x changes from xInit to xNext, then an A_i action has been performed for i=0 or 1.
        (v = [x |-> XAct(i, xInit, xNext)] <=> v'[x] != XAct(i, xInit, xNext)) \* If the value of x does not change from xInit to xNext, then it is known that no A_i action has been performed for i=0 or 1.
===============================================================================
TLC CONFIGURATION:                                                   *)
CONSTANTS v = [x |-> XInit(x)]
SPECIFICATION Spec
INVARIANTS []
**************************************************************************)
====