---- MODULE Alternate ----

(**************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009                                 *)
(* This specifies a system that alternately performs two actions, which    *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value      *)
(* alternates between 0 and 1, performing an A_0 action when v changes     *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.              *)
(**************************************************************************)

CONSTANTS   v,      \* The variable representing the part of the state that is        *)
                  \* changed by the A_0 and A_1 actions.                          *)
            XInit,  \* The constant operator representing the initial value of x. *)
            XAct   \* The constant operator representing the A_i action.        *)
VARIABLES   x,      \* The variable representing the part of the state that is    *)
                  \* changed by the A_0 and A_1 actions.                          *)
            xInit,  \* The variable representing the initial value of x.         *)
            xNext  \* The variable representing the next value of x.             *)
-----------------------------------------------------------------------------
Next ==
    \/ \E v : v = 0 /\ xInit = 0 /\ xNext = 0 \* A_0
    \/ \E v : v = 1 /\ xInit = 0 /\ xNext = 1 \* A_1
    \/ \E v : v = 0 /\ xInit = 1 /\ xNext = 0 \* A_0
    \/ \E v : v = 1 /\ xInit = 1 /\ xNext = 0 \* A_1
=============================================================================
====