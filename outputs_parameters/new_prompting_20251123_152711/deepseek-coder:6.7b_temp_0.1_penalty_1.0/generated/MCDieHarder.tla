---- MODULE MCDieHarder ----


EXTENDS Module DieHarder

CONSTANTS Goal 

VARIABLES Jug <- MCJug

CAPACITY MCCapacity ==
  IF Jug = EmptySet
  THEN EmptySet
  ELSE {1..Goal}

SPECIFICATION Spec

INVARIANTS TypeOK NotSolved

=============================================================================
====


CONSTANTS Jug, Capacity, Goal

VARIABLES 

MCJug == ...................... (* Define the set of jugs here *)

MCCapacity == ..................(* Define the capacity function here *)

Spec == ..........................(* Define the specification here *)

TypeOK == ......................(* Define the type invariant here *)

NotSolved == ..................(* Define the unsolved state here *)

=============================================================================
====

(* TLC Configuration *)
CONSTANTS Goal = 4

SPECIFICATION Spec

INVARIANTS TypeOK NotSolved
====