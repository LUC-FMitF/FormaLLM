---- MODULE MCDieHarder ----

(* The following definitions duplicate the original Die Hard problem. *)
(**************************************************************************)
MODULE DieHarder EXTENDS TLCModel
CONSTANTS Jug, Capacity, Goal, MCJug \* New constant for jug capacity
VARIABLES X1, Y1, Z1 (* Variables from the original module *)
(* The following definitions duplicate the original Die Hard problem. *)
(**************************************************************************)
DEFINE 
    MCCapacity (j : Jug), j * 2 + 10 \* Capacity is a function of jug capacity *)
INVARIANTS TypeOK NotSolved (* Invariants from the original module *)
SPECIFICATION Spec(* Specification from the original module *)
=============================================================================
CONSTANTS Goal = MCGoal, Jug <- MCJug, Capacity <- MCCapacity \* TLC configuration 
(**************************************************************************)
====