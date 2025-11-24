---- MODULE Alternate ----

(*****************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009                                *)
(*****************************************************************************)
CONSTANTS   v,            \* The variable representing the part of the state that is changed by the A_0 and A_1 actions.
            XInit,        \* The constant operator used to assert that x has a correct initial value.
            XAct          \* The constant operator used to assert that changing the value of x from xInit to xNext represents an A_i action, for i=0, 1.
VARIABLES   x             \* The part of the state changed by the A_0 and A_1 actions.
            xInit         \* The initial value of x.
            xNext         \* The next value of x after an A_i action has been performed, for i=0, 1.
------------------------------------------------------------------------------
Spec ==                   \* The specification that alternately performs two actions, which we will call A_0 and A_1.
    /\ v = [x |-> XInit(x)]        \* We let the variable x to represent the part of the state changed by the A_0 and A_1 actions.
    /\ \A i : 0..1 =>                   \* For all values of i, we have:
        (XAct(i, XInit(x), xNext) ==> v = [x |-> xNext])      \* If changing the value of x from XInit to xNext represents an A_i action, then v has a correct next value.
    /\ \A i : 0..1 =>                   \* For all values of i, we have:
        (v = [x |-> xNext] ==> XAct(i, XInit(x), xNext))      \* If v has a correct next value after an A_i action has been performed, then changing the value of x from XInit to xNext represents an A_i action.
------------------------------------------------------------------------------
THEOREM Spec => [](XAct(0, XInit(x), xNext) /\ XAct(1, XInit(x), xNext))
=============================================================================
====