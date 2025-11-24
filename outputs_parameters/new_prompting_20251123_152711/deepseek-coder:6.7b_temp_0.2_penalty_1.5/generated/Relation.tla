---- MODULE Relation ----

(***************************************************************************************)
(* This module provides some basic operations on relations, represented                 *)
(* as binary Boolean functions over some set S.                                         *)
(***************************************************************************************)

CONSTANTS   R,             \* The relation to be checked.
            S              \* Set of elements for the relation.
VARIABLES   <<vars>>       \* Variables defined in this module (if any).
----------------------------------------------------------------------------------------
Reflexive  := {(x, x) |-> TRUE}  == (* Is the relation R reflexive over S? *)
Irreflexive:= ~ Reflexive         == (* Is the relation R irreflexive over set S?*)
Symmetric  := [IF (a, b) IN R THEN (b, a) ELSE FALSE |-> TRUE]  == (* Is the relation R symmetric over set S? *)
Asymmetric:= ~(Reflexive UNION Symmetric)                           == (* Is the relation R asymmetric over set S?*)
Transitive := [IF ((a, b) IN R AND (b, c) IN R) THEN TRUE ELSE FALSE |-> TRUE]  == (* Is the relation R transitive over set S? *)
ReflexiveClosure:= ~(R UNION Reflexive)                                              == (* Compute the reflexive closure of relation R over set S.*)
TransitiveClosure := [IF ((a, b) IN (R UNION Transitive)) AND ((b, c) IN (R UNION Transitive)) THEN TRUE ELSE FALSE |-> TRUE]  == (* Compute the transitive closure of relation R over set S. *)
Connected:= ~[{(x, y): x \in dom(TransitiveClosure), y \in dom(TransitiveClosure)} - (S \times S)] == (* Is the relation R connected over set S? i.e., does there exist a path between two arbitrary elements of S? *)
----------------------------------------------------------------------------------------
TLC Configuration:
CONSTANTS  R, S={1,...,n}  ==(* Assuming n as number of elements in Set S*)
SPECIFICATION (Reflexive /\ Irreflexive /\ Symmetric /\ Asymmetric /\ Transitive /\ ReflexiveClosure /\ TransitiveClosure /\ Connected) 
INVARIANTS  <<vars>>  == (* Check if the variables are defined correctly *)
=========================================================================================
====