---- MODULE MCDieHarder ----


EXTENDS DieHarder

CONSTANTS Goal     =  4

VARIABLES Jug      <= MCJug
         Capacity <= MCCapacity

SPECIFICATION Spec

INVARIANTS TypeOK NotSolved

=============================================================================
====

(* TLC Configuration *)
CONSTANTS Goal     =  4
          Jug      <= MCJug
          Capacity <= MCCapacity 

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
====