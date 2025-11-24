---- MODULE Relation --------

(***************************************************************************)
(* This module provides some basic operations on relations, represented as     *)
(* binary Boolean functions over some set S.                             *)
(***************************************************************************)

CONSTANTS S

LOCAL INSTANCE Bool

VARIABLES R : S → S → Bool

RReflexive(s) == ∀x ∈ S : R(x, s)

RIrreflexive(s) == ∀x ∈ S : ¬R(x, s)

RSymmetric(s) == ∀x ∈ S ∀y ∈ S : R(x, y) → R(y, x)

RAsymmetric(s) == ∀x ∈ S ∀y ∈ S : ¬R(x, y) → ¬R(y, x)

RTransitive(s) == ∀x ∈ S ∀y ∈ S ∀z ∈ S : R(x, y) → R(y, z) → R(x, z)

TRansitiveClosure(s) == ∀x ∈ S : R(x, s)

RReflexiveTransitiveClosure(s) == ∀x ∈ S : R(x, s) ∧ ∀y ∈ S : R(x, y) → R(y, s)

Connected(s, t) == ∃x ∈ S : R(x, s) ∧ R(x, t)

Spec ∈ Init ∧
  RReflexive(s) ∧
  RIrreflexive(s) ∧
  RSymmetric(s) ∧
  RAsymmetric(s) ∧
  RTransitive(s) ∧
  TRansitiveClosure(s) ∧
  RReflexiveTransitiveClosure(s) ∧
  Connected(s, t)

=============================================================================
====