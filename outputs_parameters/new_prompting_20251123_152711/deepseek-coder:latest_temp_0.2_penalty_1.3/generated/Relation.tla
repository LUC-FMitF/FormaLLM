---- MODULE Relation --------

(***************************************************************************)
(* This module provides some basic operations on relations, represented as     *)
(* binary Boolean functions over some set S.                             *)
(***************************************************************************)

CONSTANTS S

VARIABLES R

\* Is the relation R reflexive over S?
Reflexive(R) ==
  FORALL x ∈ S : R(x, x)

\* Is the relation R irreflexive over set S?
Irreflexive(R) ==
  FORALL x ∈ S : ¬R(x, x)

\* Is the relation R symmetric over set S?
Symmetric(R) ==
  FORALL x, y ∈ S : R(x, y) ↔ R(y, x)

\* Is the relation R asymmetric over set S?
Asymmetric(R) ==
  FORALL x, y ∈ S : R(x, y) → R(y, x)

\* Is the relation R transitive over set S?
Transitive(R) ==
  FORALL x, y, z ∈ S : R(x, y) ∧ R(y, z) → R(x, z)

\* Compute the transitive closure of relation R over set S.
TransClosure(R) ==
  IF R ∈ S
  THEN R
  ELSE {x, y ∈ S : R(x, y) ∧ TransClosure(R)(x, y)}

\* Compute the reflexive transitive closure of relation R over set S.
ReflTransClosure(R) ==
  IF R ∈ S
  THEN TransClosure(R)
  ELSE {x, y ∈ S : R(x, y) ∧ ReflTransClosure(R)(x, y)}

\* Is the relation R connected over set S, i.e. does there exist a path *)
(* between two arbitrary elements of S?                            *)
Connected(R) ==
  FORALL x, y ∈ S : R(x, y) ↔ R(y, x)

=============================================================================
====