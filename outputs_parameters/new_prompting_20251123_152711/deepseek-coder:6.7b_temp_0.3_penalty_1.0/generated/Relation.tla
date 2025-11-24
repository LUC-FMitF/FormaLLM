---- MODULE Relation ----

(**************************************************************************)
(* This module provides some basic operations on relations, represented     *)
(* as binary Boolean functions over some set S.                             *)
(*                                                                        *)
(* Is the relation R reflexive over S?                                      *)
(*                                                                        *)
(* Is the relation R irreflexive over set S?                                *)
(*                                                                        *)<｜begin▁of▁sentence｜>
(* Is the relation R symmetric over set S?                                  *)
(*                                                                        *)
(* Is the relation R asymmetric over set S?                                 *)
(*                                                                        *)
(* Is the relation R transitive over set S?                                 *)
(*                                                                        *)
(* Compute the transitive closure of relation R over set S.                 *)
(*                                                                        *)
(* Compute the reflexive transitive closure of relation R over set S.       *)
(*                                                                        *)
(* Is the relation R connected over set S, i.e. does there exist a path     *)
(* between two arbitrary elements of S?                                     *)
(**************************************************************************)

CONSTANTS
  EmptySet == {}

\* Is the relation R reflexive over S?
IsReflexive(R, S) ==
  [x, y] \in S * S /\ x \neq y ==> R[x, y] \/ R[y, x]

\* Is the relation R irreflexive over set S?
IsIrreflexive(R, S) ==
  [x, y] \in S * S /\ x = y ==> ~R[x, y]

\* Is the relation R symmetric over set S?
IsSymmetric(R, S) ==
  [x, y] \in S * S /\ x \neq y ==> R[x, y] ==> R[y, x]

\* Is the relation R asymmetric over set S?
IsAsymmetric(R, S) ==
  [x, y] \in S * S /\ x \neq y ==> R[x, y] ==> ~R[y, x]

\* Is the relation R transitive over set S?
IsTransitive(R, S) ==
  [x, y, z] \in S * S * S /\ x \neq y /\ y \neq z /\ R[x, y] /\ R[y, z] ==> R[x, z]

\* Compute the transitive closure of relation R over set S.
TransitiveClosure(R, S) ==
  [x, y] \in S * S /\ (x = y \/ [x, y] \in R \/ [y, x] \in TransitiveClosure(R, S))

\* Compute the reflexive transitive closure of relation R over set S.
ReflexiveTransitiveClosure(R, S) ==
  [x, y] \in S * S /\ (x = y \/ [x, y] \in R \/ [y, x] \in ReflexiveTransitiveClosure(R, S))

\* Is the relation R connected over set S, i.e. does there exist a path
\* between two arbitrary elements of S?
IsConnected(R, S) ==
  [x, y] \in S * S /\ (x = y \/ [x, y] \in R \/ [y, x] \in ReflexiveTransitiveClosure(R, S))

SPECIFICATION
  IsReflexive(R, S) /\ IsIrreflexive(R, S) /\ IsSymmetric(R, S) /\
  IsAsymmetric(R, S) /\ IsTransitive(R, S) /\
  TransitiveClosure(R, S) = R \/ TransitiveClosure(R, S) \in Powerset(S * S) /\
  ReflexiveTransitiveClosure(R, S) = R \/ ReflexiveTransitiveClosure(R, S) \in Powerset(S * S) /\
  IsConnected(R, S)

INVARIANTS
  IsReflexive(R, S) ==> IsIrreflexive(R, S)
  IsSymmetric(R, S) ==> IsTransitive(R, S)
  IsAsymmetric(R, S) ==> IsTransitive(R, S)
  IsTransitive(R, S) ==> TransitiveClosure(R, S) = R \/ TransitiveClosure(R, S) \in Powerset(S * S)
  IsTransitive(R, S) ==> ReflexiveTransitiveClosure(R, S) = R \/ ReflexiveTransitiveClosure(R, S) \in Powerset(S * S)
  IsConnected(R, S) ==> ReflexiveTransitiveClosure(R, S) = R \/ ReflexiveTransitiveClosure(R, S) \in Powerset(S * S)

TLC Configuration:
CONSTANTS
  EmptySet == {}
SPECIFICATION
  IsReflexive(R, S) /\ IsIrreflexive(R, S) /\ IsSymmetric(R, S) /\
  IsAsymmetric(R, S) /\ IsTransitive(R, S) /\
  TransitiveClosure(R, S) = R \/ TransitiveClosure(R, S) \in Powerset(S * S) /\
  ReflexiveTransitiveClosure(R, S) = R \/ ReflexiveTransitiveClosure(R, S) \in Powerset(S * S) /\
  IsConnected(R, S)
INVARIANTS
  IsReflexive(R, S) ==> IsIrreflexive(R, S)
  IsSymmetric(R, S) ==> IsTransitive(R, S)
  IsAsymmetric(R, S) ==> IsTransitive(R, S)
  IsTransitive(R, S) ==> TransitiveClosure(R, S) = R \/ TransitiveClosure(R, S) \in Powerset(S * S)
  IsTransitive(R, S) ==> ReflexiveTransitiveClosure(R, S) = R \/ ReflexiveTransitiveClosure(R, S) \in Powerset(S * S)
  IsConnected(R, S) ==> ReflexiveTransitiveClosure(R, S) = R \/ ReflexiveTransitiveClosure(R, S) \in Powerset(S * S)
====