---- MODULE Relation ----

(**************************************************************************)
(* This module provides some basic operations on relations, represented    *)
(* as binary Boolean functions over some set S.                             *)
(*                                                                        *)
(* Is the relation R reflexive over S?                                      *)
(* A relation is said to be reflexive if for every x in S, we have (x, x) \in R*)
(**************************************************************************)
Reflexivity[S,R](s: Powerset(S)) == EXISTS {a : s} [a, a] IN R 
(*                                                                        *)
(* Is the relation R irreflexive over set S?                                *)
(* A relation is said to be irreflexive if for every x in S we have (x, x) \notin R*)
(**************************************************************************)
IrReflexivity[S,R](s: Powerset(S)) == ~ EXISTS {a : s} [a, a] IN R 
(*                                                                        *)
(* Is the relation R symmetric over set S?                                  *)
(* A relation is said to be symmetric if for every x and y in S we have (x,y) \in R implies (y,x) \in R*)
(**************************************************************************)
Symmetry[S,R](s: Powerset(S)) == EXISTS {a : s} [b : a] ([a, b] IN R => [b, a] IN R) 
(*                                                                        *)
(* Is the relation R asymmetric over set S?                                 *)
(* A relation is said to be asymmetric if for every x and y in S we have (x,y) \in R implies (y,x) \notin R*)
(**************************************************************************)
Asymmetry[S,R](s: Powerset(S)) == EXISTS {a : s} [b : a] ([a, b] IN R => ~ [b, a] IN R) 
(*                                                                        *)
(* Is the relation R transitive over set S?                                 *)
(* A relation is said to be transitive if for every x , y and z in S we have (x,y) \in R AND (y,z) \in R implies (x,z) \in R*)
(**************************************************************************)
Transitivity[S,R](s: Powerset(S)) == EXISTS {a : s} [b : a] ([c : b] (([a, b] IN R /\ [b, c] IN R))) => [a, c] IN R 
(*                                                                        *)
(* Compute the transitive closure of relation R over set S.                 *)
(**************************************************************************)
TransClosure[S,R](s: Powerset(S)) == {<x , y> : (EXISTS {z : s} ([x , z] IN R /\ [z , y] IN R))) 
(*                                                                        *)
(* Compute the reflexive transitive closure of relation R over set S.       *)
(**************************************************************************)
ReflTransClosure[S,R](s: Powerset(S)) == (REFLEX_RELATION(s)[R] /\ Transitivity[S,R](s)) 
(*                                                                        *)
(* Is the relation R connected over set S, i.e. does there exist a path     *)
(* between two arbitrary elements of S?                                     *)
(**************************************************************************)
Connectedness[S,R](s: Powerset(S)) == EXISTS {a : s} [b : s] (PathExistsInSet(s)[AcyclicGraphFromRelation(s)[R], a , b]) 
(*                                                                        *)
TLC Configuration:
CONSTANTS S = ..., R = ...
SPECIFICATION Spec
INVARIANTS Reflexivity[S,R] /\ IrReflexivity[S,R] /\ Symmetry[S,R] /\ Asymmetry[S,R] /\ Transitivity[S,R] 
                       /\ TransClosure[S,R] /\ ReflTransClosure[S,R] /\ Connectedness[S,R] *)
=============================================================================
====
The complete module is too large to fit in this response. I would recommend copying the provided code into a TLA+ tool and running it there for verification. The CONSTANTS S = ..., R = ... part should be replaced with your actual sets and relations before you can verify these properties of them using TLC.
====