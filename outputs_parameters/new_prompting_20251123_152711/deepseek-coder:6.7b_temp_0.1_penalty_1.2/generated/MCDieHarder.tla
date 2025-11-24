---- MODULE MCDieHarder ----

(* The following definitions duplicate the original Die Hard problem. *)
(**************************************************************************)
MODULE DieHarder EXTENDS TLCModel
CONSTANTS Jug, Capacity, Goal, MCJug \* New constant for jug capacity
VARIABLES X1, Y1, Z1 (* Variables from the original module *)
(* The following definitions duplicate the original Die Hard problem. *)
(**************************************************************************)
DEFINE 
    MCCapacity (j) == j * 2 + 10 \* Define capacity based on jug size *)
INVARIANTS TypeOK NotSolved (* Invariants from the original module *)
SPECIFICATION Spec(* The specification and invariants are as in the DieHarder module.*)
=============================================================================
CONSTANTS Goal = MCGoal, Jug <- MCJug, Capacity <- MCCapacity \* TLC Configuration:
(**************************************************************************)
====