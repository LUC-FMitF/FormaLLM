---- MODULE Alternate ----

(*************************************************************************)
(* This specifies a system that alternately performs two actions, which  *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value    *)
(* alternates between 0 and 1, performing an A_0 action when v changes   *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.            *)
(*************************************************************************)
CONSTANTS XInit, XAct : SET
VARIABLES x : VALUE \* The part of the state that is changed by the     *)
                    \* A_0 and A_1 actions.                                *)
-----------------------------------------------------------------------------
INITIAL x = XInit
-----------------------------------------------------------------------------
Next ==
  /\ [](x' = IF v=0 THEN XAct(0, x, x+1) ELSE XAct(1, x-1, x))
  \/ (v' = v)
***************************************************************************)
====