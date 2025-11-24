---- MODULE MCDieHarder ----

(******************************************************************************************)
(* The following definitions duplicate the original Die Hard problem.                     *)
(* To have TLC find a solution, we must tell it what values to use for the               *)
(* constant parameters Jug, Capacity, and Goal. However, TLC does not allow one          *)
(* to write function-valued expressions in a configuration file. So, we use this           *)
(* module, which extends module DieHarder, to define a function MCCapacity               *)
(* and have the configuration file TLC to substitute MCCapacity for Capacity.            *)
(* Since we need to know the value of Jug to define Capacity (which is a                 *)
(* function having Jug as its domain),  we also define MCJug and tell                     *)
(* TLC to substitute it for Jug.                                                         *)
(******************************************************************************************)

EXTENDS DieHarder
CONSTANTS Goal     = <value>    \* The goal amount of liquid in the jug
          Capacity  <- MCCapacity  \* Maximum capacity of each jug
           Jug      <- MCJug       \* Set of all possible jars' capacities.
SPECIFICATION Spec
INVARIANTS TypeOK NotSolved   \* The type invariant and the specification for this module.
=============================================================================
CONSTANTS Goal = <value>, Jug <<>>, Capacity = 0  (* Replace with actual values *)
====