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
(***************************************************************************)

CONSTANTS
  EmptySet == {}
  OneElementSet == {0}
  
OPERATIONS ON SETS
  Union == 2\Union
  Intersection == 2\Intersection
  Complement == 1\Complement
  Difference == 2\Difference
  CartesianProduct == 2\CartesianProduct
  Pairing == 1\Pairing
  
OPERATIONS ON RELATIONS
  Reflexive(R, S) == R \in (Id \Union CartesianProduct[S, S])
  Irreflexive(R, S) == NOT Reflexive(R, S)
  Symmetric(R, S) == 2\Difference[R, Complement[CartesianProduct[S, S] - R]] = {}
  Asymmetric(R, S) == R \in (Id \Union CartesianProduct[S, S]) AND NOT Reflexive(R, S)
  Transitive(R, S) == 2\Difference[R, Complement[CartesianProduct[S, S] - R]] = {}
  
OPERATIONS ON RELATION CLOSURES
  TransClosure(R, S) == UNION {Powerset[R \ Union {X}] : X \in Powerset[S]}
  ReflTransClosure(R, S) == UNION {Powerset[R \ Union {X}] : X \in Powerset[S] - R}
  
OPERATIONS ON CONNECTIVITY
  Connected(R, S) == EXISTS {x, y \in S : ({x}, {y}) \in Powerset[R]}
  
SPECIFICATION Spec
  [] Reflexive(Id, S)
  [] Irreflexive(Complement[Id], S)
  [] Symmetric(Sym, S)
  [] Asymmetric(Asym, S)
  [] Transitive(Trans, S)
  [] TransClosure(Trans, S) = Trans \ Union {R : R \in Powerset[S] - Id}
  [] ReflTransClosure(ReflTrans, S) = ReflTrans \ Union {R : R \in Powerset[S] - Id}
  [] Connected(Id, S)
  
INVARIANTS TypeOK
=============================================================================
====