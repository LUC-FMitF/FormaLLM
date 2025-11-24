---- MODULE MCDieHarder ----

(***************************************************************************)
(* The following definitions duplicate the original Die Hard problem.          *)
(****************************************************************************)
EXTENDS ModuleDieHarder
  
CONSTANTS JugSize = 5 (* You can set this in your TLC config file *)
           MCJug = [i \in 1..JugSize |-> i] (* Array of natural numbers from 1 to JugSize *)
           
(* The total amount that can be measured by Capacity jags. This is a function having Jug as its domain, so we define it here and tell TLC to substitute MCCapacity for Capacity in the config file.*)
MCCapacity == SUM [i \in 1..JugSize |-> i] * MCJug[Capacity] (* Sum of all jug capacities *)
  
(* The specification is unchanged from ModuleDieHarder, so we just extend it here: *)
Spec == /\ Init /\ ([](Pour) U {](Empty)) >< [](Fill Jug1) \/ [](Fill Jug2)
    === ((Jug1 = MCJug[Capacity] * Goal) V (Jug2 = 0))
  
(* The invariant is unchanged from ModuleDieHarder, so we just extend it here: *)
NotSolved == /\ NotEmpty(Jug1) \/ Empty(Jug2) >< Jug1 =< Capacity[Goal] - Goal * MCJug[Capacity]
  
=============================================================================
(* TLC Configuration File for DieHarderExtended: *)
CONSTANTS Goal     = 4 (* You can set this in your config file. *)
          Jug      <- MCJug 
          Capacity <- MCCapacity 
          
SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
=============================================================================