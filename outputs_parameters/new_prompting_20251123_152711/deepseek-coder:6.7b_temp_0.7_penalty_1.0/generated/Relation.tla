---- MODULE Relation ----

(***************************************************************************)
(* This module provides some basic operations on relations, represented     *)
(* as binary Boolean functions over some set S.                             *)
(***************************************************************************)

CONSTANTS   S,             \* The set of all elements
            R              \* The relation between S

VARIABLES   Reflexive,      \* Is the relation R reflexive over S?
            Irreflexive,    \* Is the relation R irreflexive over set S?
            Symmetric,      \* Is the relation R symmetric over set S?
            Asymmetric,     \* Is the relation R asymmetric over set S?
            Transitive,     \* Is the relation R transitive over set S?
            TransClosure,   \* The transitive closure of relation R over set S.
            ReflTransClosure, \* The reflexive transitive closure of relation R over set S.
            Connected       \* Is the relation R connected over set S, i.e. does there exist a path
                                between two arbitrary elements of S?

\* Is the relation R reflexive over S?
Reflexive(R,S) == \E x \in S : R(x,x)

\* Is the relation R irreflexive over set S?
Irreflexive(R,S) == \A x \in S : \neg R(x,x)

\* Is the relation R symmetric over set S?
Symmetric(R,S) == \E x, y \in S : R(x,y) => R(y,x)

\* Is the relation R asymmetric over set S?
Asymmetric(R,S) == \E x, y \in S : R(x,y) => \neg R(y,x)

\* Is the relation R transitive over set S?
Transitive(R,S) == \E x, y, z \in S : R(x,y) /\ R(y,z) => R(x,z)

\* The transitive closure of relation R over set S.
TransClosure(R,S) == {(x,y) \in S \times S : \E z : R(x,z) /\ R(z,y)}

\* The reflexive transitive closure of relation R over set S.
ReflTransClosure(R,S) == R \cup TransClosure(R,S)

\* Is the relation R connected over set S, i.e. does there exist a path
\* between two arbitrary elements of S?
Connected(R,S) == \E x, y \in S : (x,y) \in ReflTransClosure(R,S)

Spec == [] \E x, y \in S : R(x,y) = R(y,x)

TLC configuration:
CONSTANTS S = {1,2,3}
SPECIFICATION Spec
INVARIANTS [Reflexive(R,S), Irreflexive(R,S), Symmetric(R,S), Asymmetric(R,S), Transitive(R,S),
              TransClosure(R,S) = TransClosure(R,S), ReflTransClosure(R,S) = ReflTransClosure(R,S),
              Connected(R,S)]
=============================================================================
====

This TLA+ specification includes various predicates to check if a relation is reflexive, irreflexive, symmetric, asymmetric, transitive, and connected. It also includes computations for the transitive closure and the reflexive transitive closure of a relation. The TLC configuration specifies the set S and the invariants to be checked.
====