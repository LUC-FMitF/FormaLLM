---- MODULE Relation ----

(***************************************************************************)
(* This module provides some basic operations on relations, represented     *)
(* as binary Boolean functions over some set S.                             *)
(*                                                                         *)
(* Is the relation R reflexive over S?                                      *)
(*                                                                         *)
(* Is the relation R irreflexive over set S?                                *)
(*                                                                         *)
(* Is the relation R symmetric over set S?                                  *)
(*                                                                         *)
(* Is the relation R asymmetric over set S?                                 *)
(*                                                                         *)
(* Is the relation R transitive over set S?                                 *)
(*                                                                         *)
(* Compute the transitive closure of relation R over set S.                 *)
(*                                                                         *)
(* Compute the reflexive transitive closure of relation R over set S.       *)
(*                                                                         *)
(* Is the relation R connected over set S, i.e. does there exist a path     *)
(* between two arbitrary elements of S?                                     *)
(*                                                                         *)
(***************************************************************************)

CONSTANTS
  EmptySet == {}
  OneElementSet == {0}

VARIABLES
  R, S

ASSUME
  R \in Powerset(S)
  S \in Powerset(S)

DEFINITIONS
  Reflexive(R) == \A x \in S : R(x, x)
  Irreflexive(R) == \A x \in S : ~R(x, x)
  Symmetric(R) == \A x, y \in S : R(x, y) => R(y, x)
  Asymmetric(R) == \A x, y \in S : R(x, y) /\ ~R(y, x) => x = y
  Transitive(R) == \A x, y, z \in S : R(x, y) /\ R(y, z) => R(x, z)
  TransitiveClosure(R) == \A x, y \in S : Path(R, x, y)
  ReflexiveTransitiveClosure(R) == \A x, y \in S : R(x, y) \/ Path(R, x, y)
  Connected(R) == \A x, y \in S : Path(R, x, y)

THEOREMS
  Theorem1 == Reflexive(R) => TransitiveClosure(R) = R
  Theorem2 == Irreflexive(R) => TransitiveClosure(R) \= R
  Theorem3 == Symmetric(R) => TransitiveClosure(R) = R
  Theorem4 == Asymmetric(R) => TransitiveClosure(R) = R
  Theorem5 == Transitive(R) => TransitiveClosure(R) = R
  Theorem6 == Reflexive(R) => ReflexiveTransitiveClosure(R) = R
  Theorem7 == Transitive(R) => ReflexiveTransitiveClosure(R) = R
  Theorem8 == Connected(R) => ReflexiveTransitiveClosure(R) = R

TLC Configuration
  CONSTANT EmptySet = {}
  CONSTANT OneElementSet = {0}
  VARIABLE R, S
  ASSUME R \in Powerset(S)
  ASSUME S \in Powerset(S)
  DEFINE Reflexive(R) == \A x \in S : R(x, x)
  DEFINE Irreflexive(R) == \A x \in S : ~R(x, x)
  DEFINE Symmetric(R) == \A x, y \in S : R(x, y) => R(y, x)
  DEFINE Asymmetric(R) == \A x, y \in S : R(x, y) /\ ~R(y, x) => x = y
  DEFINE Transitive(R) == \A x, y, z \in S : R(x, y) /\ R(y, z) => R(x, z)
  DEFINE TransitiveClosure(R) == \A x, y \in S : Path(R, x, y)
  DEFINE ReflexiveTransitiveClosure(R) == \A x, y \in S : R(x, y) \/ Path(R, x, y)
  DEFINE Connected(R) == \A x, y \in S : Path(R, x, y)
  THEOREM Theorem1 == Reflexive(R) => TransitiveClosure(R) = R
  THEOREM Theorem2 == Irreflexive(R) => TransitiveClosure(R) \= R
  THEOREM Theorem3 == Symmetric(R) => TransitiveClosure(R) = R
  THEOREM Theorem4 == Asymmetric(R) => TransitiveClosure(R) = R
  THEOREM Theorem5 == Transitive(R) => TransitiveClosure(R) = R
  THEOREM Theorem6 == Reflexive(R) => ReflexiveTransitiveClosure(R) = R
  THEOREM Theorem7 == Transitive(R) => ReflexiveTransitiveClosure(R) = R
  THEOREM Theorem8 == Connected(R) => ReflexiveTransitiveClosure(R) = R
====