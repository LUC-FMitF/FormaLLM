---- MODULE Relation ----

(**************************************************************************)
(* This module provides some basic operations on relations, represented  *)
as binary Boolean functions over some set S.                            *)
(**************************************************************************)

CONSTANTS   R,        \* The relation to operate on.
            S         \* The set of elements in the relation.
VARIABLES   reflexive,  \* Is the relation reflexive over set S?
            irreflexive, \* Is the relation irreflexive over set S?
            symmetric,  \* Is the relation symmetric over set S?
            asymmetric, \* Is the relation asymmetric over set S?
            transitive, \* Is the relation transitive over set S?
            transClosure, \* The transitive closure of relation R over set S.
            reflexiveTransClosure   \* The reflexive transitive closure of relation R over set S.
----------------------------------------------------------------------------

Init ==
    /\ R \in [S -> S -> Bool]
    /\ S \in FiniteSet
    /\ reflexive = Forall x \in S: (R(x,x))
    /\ irreflexive = Forall x, y \in S: (NOT (R(x,y) AND x=y))
    /\ symmetric = Forall x, y \in S: ((R(x,y) <-> R(y,x)))
    /\ asymmetric = Forall x, y \in S: ((R(x,y) AND R(y,x)) => x=y)
    /\ transitive = Forall x, y, z \in S: (R(x,y) AND R(y,z) => R(x,z))
    /\ transClosure = [x, y |-> (R(x,y) OR (FORALL w \in S: R(w,x) /\ R(w,y))) ]
    /\ reflexiveTransClosure = [x, y |-> ((R(x,y) OR (FORALL w \in S: R(w,x) /\ R(w,y))) AND x=y)]
=============================================================================
====