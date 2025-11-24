---- MODULE Alternate ----

(**************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009                               *)
(* This specifies a system that alternately performs two actions, which    *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value      *)
(* alternates between 0 and 1, performing an A_0 action when v changes     *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.              *)
(**************************************************************************)

CONSTANTS   XInit,    \* The initial predicate.
            XAct,     \* The transition relation.
            v         \* The variable representing the alternating actions.
VARIABLES   x         \* The part of the state that is changed by the A_0 and A_1 actions.
----------------------------------------------------------------------------
Next == \* The next-state relation.
    \/ \E v : Spec
    \/ XInit(x) /\ \A v : XAct(v, x, x') /\ Next(x')

Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<x>>

=============================================================================
====