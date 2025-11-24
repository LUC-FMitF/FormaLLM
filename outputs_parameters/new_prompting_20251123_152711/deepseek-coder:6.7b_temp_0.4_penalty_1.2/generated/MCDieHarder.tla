---- MODULE MCDieHarder ----
EXTENDS ModuleName(s) := { DIEHARDER }  (* replace with the name of your original die hard module *)
=============================================================================
(* The following definitions duplicate the original Die Hard problem.*)
-----------------------------------------------------------------------------
CONSTANTS Goal     =  4                   (* TLC configuration: *)
          Jug      <- MCJug                (* substitute this for actual value later in config file, or use a tool to generate it automatically *)
          Capacity <- MCCapacity           (* same here*)

SPECIFICATION Spec                            (* Tell TLA+ what you want to prove: the specification. *)
INVARIANTS TypeOK NotSolved                   (* Postcondition for your module's correctness property, i.e., it is okay if we don't solve all instances of this problem yet*)
=============================================================================
(* Specification and invariants go here... *)
-----------------------------------------------------------------------------
====