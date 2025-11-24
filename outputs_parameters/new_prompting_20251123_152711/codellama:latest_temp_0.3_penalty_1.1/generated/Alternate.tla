---- MODULE Alternate ----

(**************************************************************************)
(* This specifies a system that alternately performs two actions, which    *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value      *)
(* alternates between 0 and 1, performing an A_0 action when v changes     *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.              *)
(**************************************************************************)

CONSTANTS   XInit,    \* The initial state predicate.
            XAct,     \* The transition relation.
            v         \* The variable representing the alternating actions.
VARIABLES   x         \* The part of the state that is changed by the A_0 and A_1 actions.
----------------------------------------------------------------------------
Spec ==                                                                    *)
    /\ [][XInit]_<<x>>                                                     *)
    /\ [][XAct]_<<v, xInit, xNext>>                                        *)
    /\ \A v : Spec                                                         *)
=============================================================================
====