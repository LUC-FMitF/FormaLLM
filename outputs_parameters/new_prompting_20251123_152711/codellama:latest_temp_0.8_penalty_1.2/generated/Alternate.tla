---- MODULE Alternate ----

(**************************************************************************)
(* This specifies a system that alternately performs two actions, which    *)
* for now I will call A_0 and A_1.  It uses a variable v whose value      *)
* alternates between 0 and 1, performing an A_0 action when v changes     *)
* from 0 to 1, and an A_1 action when v changes from 1 to 0.              *)
(**************************************************************************)
VARIABLES v : {0, 1}
CONSTANTS XInit, XAct : {Nat -> Bool}
ASSUME
  /\ \E v \in {0, 1} :                   \* This is the initial state.    *)
      XInit(v)
/\ \A v \in {0, 1} :                     \* We'll alternate actions.       *)
      AXACT(v)
------------------------------------------------------------------------------
ALTERNATES                                                               
A_0 == \E v \in {0} :                    \* Action A_0 always occurs.     *)
     /\ XInit(v)            \* The action is valid.                      *)
     /\ XAct(0, v, 1)       \* We change the value to 1.                *)
A_1 == \E v \in {1} :                    \* Action A_1 always occurs.     *)
     /\ XInit(v)            \* The action is valid.                      *)
     /\ XAct(1, v, 0)       \* We change the value to 0.                *)
------------------------------------------------------------------------------
INITIALISATION                                                            
/\ v = 0                                        \* Initialize v.*)
-----------------------------------------------------------------------------
TRANSITION                                                             
/\ AXACT(v)           \* We perform an action based on the state. *)
=============================================================================
====