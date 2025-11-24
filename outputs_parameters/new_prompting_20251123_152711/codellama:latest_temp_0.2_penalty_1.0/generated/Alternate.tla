---- MODULE Alternate ----

(**************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009                                 *)
(**************************************************************************)

CONSTANTS   v,          \* The variable representing the part of the state that is changed by the A_0 and A_1 actions.
            XInit,      \* The constant operator representing the initial value of x.
            XAct        \* The constant operator representing the A_i action, for i=0, 1.
VARIABLES   x           \* The part of the state that is changed by the A_0 and A_1 actions.

Init == \* The initial predicate.
    /\ x = XInit

Next == \* The next-state relation.
    \/ \E v : v = 0 /\ x = XAct(0, XInit, XInit)
    \/ \E v : v = 1 /\ x = XAct(1, XInit, XInit)

Spec == \* The specification.
    Init /\ [][Next]_<<v, x>>

=============================================================================
====