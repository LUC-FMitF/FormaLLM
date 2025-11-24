---- MODULE MCDieHarder ---------------------------------- IMPORT Naturals -----
EXTENDS TLCBench DIEHARD, Liveness
----------------------------------------------------------- DieHarderExtended ---
(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.       *)
(* To have TLC find a solution, we must tell it what values to use for      *)
(* constant parameters Jug, Capacity, and Goal.  However, TLC does not     *)
(* allow one to write function-valued expressions in a configuration        *)
(* file.  So, we use this module, which extends module DieHarderExtended   *)
(* to define functions MCCapacity(Jug) and MCGoal() for Capacity           *)
(* (which is a function having Jug as its domain), Goal - the state after    *)
(* n steps. Since we need to know the value of Jug to define Capacity      *)
(* or Goal,  we also define functions MCJug and tell TLC to substitute it   *)
(* for Jug in our configuration file (i.e., DieHarderExtended_Config).    *)
(**************************************************************************)

CONSTANTS Capacity <- MCCapacity[MCJug]
          Goal     <- MCGoal()
====