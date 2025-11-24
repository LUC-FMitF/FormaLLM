---- MODULE Alternate ----

(**************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009                                                                       *)
(**************************************************************************)

CONSTANTS   v,  \* The variable that alternates between 0 and 1.
            XInit,  \* The operator that asserts the initial value of x.
            XAct   \* The operator that asserts the value of x after an A_i action, for i=0, 1.
VARIABLES   x

Init == \* The initial predicate.
    /\ x = XInit(x)

Next == \* The next-state relation.
    \/ \E v : v = 0 /\ x = XAct(0, XInit(x), XInit(x))  \* Perform an A_0 action.
    \/ \E v : v = 1 /\ x = XAct(1, XInit(x), XInit(x))  \* Perform an A_1 action.

Spec == \* The specification predicate.
    Init /\ [][Next]_<<v, x>>

=============================================================================
====