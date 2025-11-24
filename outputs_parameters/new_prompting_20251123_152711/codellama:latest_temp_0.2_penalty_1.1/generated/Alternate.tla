---- MODULE Alternate ----

(***************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009                               *)
(***************************************************************************)

CONSTANTS   v,            \* The variable representing the part of the state that is changed by the A_0 and A_1 actions.
            XInit,        \* The constant operator representing the initial value of x.
            XAct          \* The constant operator representing the change in x between two values.
VARIABLES   x             \* The part of the state that is changed by the A_0 and A_1 actions.
------------------------------------------------------------------------------
Init == \* The initial predicate.
    /\ v = 0
    /\ x = XInit(x)

Next == \* The next-state relation.
    \/ \E i : i = 0 \/ i = 1
    \/ \E i : i = 0 & v = 0 => x' = XAct(i, x, x')
    \/ \E i : i = 1 & v = 1 => x' = XAct(i, x, x')

Spec == \* The specification.
    Init /\ [][Next]_<<v, x>>
------------------------------------------------------------------------------
THEOREM Spec => [](XInit(x) /\ XAct(i, XInit(x), XAct(i, x, x')) ==> x' = XAct(i, x, x'))
=============================================================================
====