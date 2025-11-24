---- MODULE MCConsensus ----

(**************************************************************************)
(*                                                                        *)
(* This module checks the specification of a system with respect to its  *)
(* invariants. The spec is defined in ISpec, and the invariant is         *)
*defined in Inv.                                                          *)
(**************************************************************************)

CONSTANTS Value = {"a", "b", "c"}
SPECIFICATION ISpec
INVARIANT Inv
CHECK_DEADLOCK FALSE
====