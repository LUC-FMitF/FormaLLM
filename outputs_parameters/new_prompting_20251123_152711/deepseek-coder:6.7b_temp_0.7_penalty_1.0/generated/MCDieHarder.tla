---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.             *)
(**************************************************************************)

(* Extending DieHarder module to allow TLC to find solution for Capacity *)
CONSTANTS 
    MCCapacity(Jug) == IF Jug = 0 THEN 0 ELSE 1
    MCJug == ------------ CHOOSE i \in 0..100 : i

(* Using the extended DieHarder module *)
EXTENDS DieHarder

(* The specification to be proved *)
SPECIFICATION Spec

(* The invariant to be maintained *)
INVARIANTS TypeOK NotSolved

=============================================================================
====

The configuration file for TLC would look something like this:

(**************************************************************************)

(* TLC Configuration *)
CONSTANTS 
    Goal     = 4
    Jug      = ------------ CHOOSE i \in 0..100 : i
    Capacity = [i \in 0..100  --> 1]

(* Model Checking *)
SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

=============================================================================
====

Please note that the values for Jug and Capacity are chosen arbitrarily in the configuration file for TLC, and the actual values would be determined by the TLC model checker.
====