---- MODULE Relation --------

(*********************************************************************** *)
(* This module provides some basic operations on relations, represented as   *)
(* binary Boolean functions over set S.                                *)
(***********************************************************************)
                                                                       (* Is the relation R reflexive?                                                    *)
LOCAL INSTANCE Reflexivity  RELATIONS r = <<r: Set<Set>>;    \* The predicate isReflexive iff for all x in S, (x -> r(x)) holds.   *//** Is the relation R irreflexive?                                                    *)
LOCAL INSTANCE Irreflexivity RELATIONS r = <<r: Set<Set>>;    \* The predicate isIrreflexive iff for all x in S, (¬(x -> ¬R)) holds.   *//** Is the relation R symmetric?                                                    *)
LOCAL INSTANCE Symmetry RELATIONS r = <<r: Set<Set>>;    \* The predicate isSymmetric iff for all x and y in S, (xy ↔ yx).     *//** Compute transitive closure of relation R over set S.                                                    *)
LOCAL INSTANCE Transitivity RELATIONS r = <<r: Set<Set>>;    \* The predicate isTransitive iff for all x and y in S, (xy ↔ xz).     *//** Compute the reflexive transitive closure of relation R over set S.                                                    *)
LOCAL INSTANCE Connectivity RELATIONS r = <<r: Set<Set>>;    \* The predicate isConnected iff for all pair (x, y) in P there exists a path from x to y using the function f(u).   *//** Is relation R connected?                                                    *)
=============================================================================
----- END MODULE Relations ----- -------- End of Comments --- TLC Configuration: CONSTANTS <constant> = <value>  SPECIFICATION Spec INVARIANTS <<names>>; --+-- */* Defines operators on finite zero-indexed sequences, where a sequence of length n is represented as a function whose domain is the set 0..(n−1) (the set {0,…,(n - 1}). *)
====