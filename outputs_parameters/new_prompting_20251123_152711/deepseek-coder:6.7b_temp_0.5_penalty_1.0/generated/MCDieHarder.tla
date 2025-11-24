---- MODULE MCDieHarder ----

(***************************************************************************)
(* The following definitions duplicate the original Die Hard problem.         *)
(* To have TLC find a solution, we must tell it what values to use for the    *)
(* constant parameters Jug, Capacity, and Goal.  However, TLC does not allow *)
(* one to write function-valued expressions in a configuration file.  So, we  *)
(* use this module, which extends module DieHarder, to define a function    *)
(* MCCapacity and have the configuration file TLC to substitute MCCapacity  *)
(* for Capacity.  Since we need to know the value of Jug to define Capacity *)
(* (which is a function having Jug as its domain), we also define MCJug and  *)
(* tell TLC to substitute it for Jug.                                      *)
(***************************************************************************)

EXTENDS Module DieHarder

CONSTANTS Goal     = \* The goal amount of water
          Jug      = \* The size of the jug
          Capacity = \* The capacity of the jug

VARIABLES MCJug, \* The size of the jug for model checking
         MCCapacity \* The capacity of the jug for model checking

ASSUME \* Assume the capacity of the jug is the same as the size
  Capacity = Jug

\* The invariant that checks if the system is in a valid state
TypeOK == Jug > Goal \/ Capacity > Goal

\* The invariant that checks if the system has not been solved yet
NotSolved == Jug \in N \/ Capacity \in N

=============================================================================
====

(* TLC Configuration *)
CONSTANTS Goal     = \* The goal amount of water
          Jug      <- MCJug \* The size of the jug
          Capacity <- MCCapacity \* The capacity of the jug

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
====