---- MODULE EWD998ChanID_export ----

(*****************************************************************************)
(* Comments *)
(*****************************************************************************)

CONSTANTS   Node = {n1, n2, n3, n4, n5, n6, n7}
VARIABLES   VectorClock <<Node -> NAT>>

-------------------------------------------------------------------------------
Init == (* Fewer initial states to speed-up startup. *)
    /\ VectorClock = [n -> (IF n IN Node THEN 0 ELSE OMEGA)] FORALL n IN Node

Spec == (* TerminationDetected occurs within N steps where N has been chosen arbitrarily. *)
    [](\A i : Node -> F(VectorClock[i] = 1)) WITHIN 7

PostInv == (* Rule 0 *)
    ==> [](VectorClock'[n] = IF n IN Node THEN VectorClock[n] + 1 ELSE OMEGA)
    /\ [](\A i,j : Node -> (i != j IMP VectorClock'[i] >= VectorClock[j]))

JsonInv == (* EWD840 *)
    ==> Json(VectorClock)(NODE_NAME = "vectorClock")
    /\ [](\A n : Node -> IS_JSON(n, VectorClock[n]))

(* TLC Configuration: *)
CONSTANTS  
    Node = {n1, n2, n3, n4, n5, n6, n7}
    Init <- MCInit \* Fewer initial states to speed-up startup.
SPECIFICATION
    Spec /\ JsonInv /\ PostInv
INVARIANT 
    PostInv
CHECK_DEADLOCK 
    FALSE
===============================================================================
====