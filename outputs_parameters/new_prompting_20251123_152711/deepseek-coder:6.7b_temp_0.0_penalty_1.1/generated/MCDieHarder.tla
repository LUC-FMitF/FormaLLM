---- MODULE MCDieHarder ----
EXTENDS Module DieHard

CONSTANTS Jug = MCJug  (* Use function-valued expression for Jug *)
           Capacity = MCCapacity  (* Use function-valued expression for Capacity *)

FUNCTIONS
    MCCapacity == IF Jug = 1 THEN 4 ELSE 3  (* Define Capacity based on Jug *)
    MCJug(j) == 2 - j  (* Define Jug based on its index in the domain of Capacity *)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
=============================================================================
====