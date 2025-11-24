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

RAsymmetric(s) == ∀x ∈ S ∀y ∈ S : ¬R(x, y) → R(x, y)

RTransitive(s) == ∀x ∈ S ∀y ∈ S ∀z ∈ S : R(x, y) → R(y, z) → R(x, z)

RTransClosure(s) == ∀x ∈ S ∀y ∈ S : R(x, y) → R(y, s)

RReflTransClosure(s) == ∀x ∈ S : R(x, s) → R(x, y) → R(y, s)

RConnected(s, t) == ∃x ∈ S : R(x, s) ∧ R(x, t)

Spec ∀x ∈ S : R(x, s) → R(x, t) → R(x, s) → R(x, t)

Theorems RReflexive, RIrreflexive, RSymmetric, RAsymmetric, RTransitive, RTransClosure, RReflTransClosure, RConnected
=============================================================================
====