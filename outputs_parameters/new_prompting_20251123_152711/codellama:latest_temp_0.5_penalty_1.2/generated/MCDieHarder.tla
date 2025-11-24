---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.   *)
(* However, TLC does not allow one to write function-valued expressions  *)
(* in a configuration file. So, we use this module, which extends        *)
(* module DieHarder, to define a function MCCapacity and have the       *)
(* configuration file TLC substitute MCCapacity for Capacity. Since      *)
(* we need to know the value of Jug to define Capacity (which is a       *)
(* function having Jug as its domain), we also define MCJug and tell     *)
(* TLC to substitute it for Jug.                                          *)
(**************************************************************************)

CONSTANTS   Goal,        \* The goal number of units in the jug.
            Capacity    \* The capacity of the jug.
VARIABLES   Jug         \* The current contents of the jug.
            Empty       \* A predicate indicating whether or not the     *)
                          (* jug is empty.                                *)
-----------------------------------------------------------------------------
MCJug ==    \* Choose something to represent the absence of a value.
    CHOOSE v : v \notin {0, 1}

MCCapacity(j) ==   \* The capacity of the jug for given j.
    IF j = MCJug THEN Capacity ELSE 2 * j - 1

Init == \* The initial predicate.
    /\ Jug = MCJug
    /\ Empty = TRUE
    
Next == \* The next-state relation.
    [][
        /***********************/
        /* Goal: Fill the jug to */
        /*   its capacity       */
        /***********************/
        
        IF (Jug < Capacity) THEN
            /\ Jug' = Capacity
            /\ Empty' = FALSE
        ELSE
          \* Stay at current state
          /\ Jug' = Jug
          /\ Empty' = Empty
          
        /***********************/
        /* Goal: Pour from the */
        /*   jug into a cup    */
        /***********************/
        
        IF (Jug > 0) THEN
            /\ Cup' = Cup + Jug
            /\ Jug' = 0
        ELSE
          \* Stay at current state
          /\ Cup' = Cup
          /\ Jug' = Jug
          
        /***********************/
        /* Goal: Pour from a cup */
        /*   into the jug       */
        /***********************/
        
        IF (Cup > 0) THEN
            /\ Cup' = Cup - 1
            /\ Jug' = Jug + 1
        ELSE
          \* Stay at current state
          /\ Cup' = Cup
          /\ Jug' = Jug
          
        /***********************/
        /* Goal: Empty the jug   */
        /*   and a cup          */
        /***********************/
        
        IF (Jug > 0 OR Cup > 0) THEN
            /\ Cup' = 0
            /\ Jug' = 0
            /\ Empty' = TRUE
        ELSE
          \* Stay at current state
          /\ Cup' = Cup
          /\ Jug' = Jug
          /\ Empty' = Empty
      ]_<<Jug, Cup, Empty>>
        
Spec == \* Initialize state with Init and transition with Next.
    [][Init]_<<Jug, Cup, Empty>><[Next]_<<Jug, Cup, Empty>>
-----------------------------------------------------------------------------
THEOREM Spec => Goal = Capacity /\ (EXISTS j : Jug = MCCapacity(j))
=============================================================================
====