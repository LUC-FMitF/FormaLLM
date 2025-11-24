---- MODULE Alternate ----

(***************************************************************************)
(* This specifies a system that alternately performs two actions, which    *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value      *)
(* alternates between 0 and 1, performing an A_0 action when v changes     *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.              *)
(***************************************************************************)

CONSTANTS   \* The variable that alternates between 0 and 1,                *)
           v                                                            *)
VARIABLES   \* The part of the state that is changed by the A_0          *)
            \* and A_1 actions.                                             *)
            x                                                            *)
CONSTANTS   \* Constant operators for assuming correctness of initial     *)
           XInit,    \* and actions.                                        *)
           XAct                                                         *)
-----------------------------------------------------------------------------
Next ==  \* The next-state relation.                                      *)
       /\ \A i : v = i \/ \A i : v = 1 - i                                *)
       /\ \E xInit, xNext : XInit(x) =>                                   *)
          (IF v = 0 THEN XAct(v, xInit, xNext)                            *)
           ELSE XAct(1 - v, xNext, xInit))                                *)
=============================================================================
====[/INST:
====