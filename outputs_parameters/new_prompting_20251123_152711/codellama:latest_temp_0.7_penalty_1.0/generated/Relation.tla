---- MODULE Relation ----

(**************************************************************************)
(* This module provides some basic operations on relations, represented *)
as binary Boolean functions over some set S.                            *)
(**************************************************************************)

CONSTANTS   S,         \* The set of all elements.
            R          \* The relation R over S.
VARIABLES   x, y,      \* Variables for elements of S.
            r          \* Variables for relations.
----------------------------------------------------------------------------

IsReflexive(R) == \* Is the relation R reflexive over set S?
    \A x \in S : R[x, x]

IsIrreflexive(R) == \* Is the relation R irreflexive over set S?
    \A x \in S : NOT R[x, x]

IsSymmetric(R) == \* Is the relation R symmetric over set S?
    \A x, y \in S : (R[x, y] => R[y, x])

IsAsymmetric(R) == \* Is the relation R asymmetric over set S?
    \A x, y \in S : (R[x, y] => NOT R[y, x])

IsTransitive(R) == \* Is the relation R transitive over set S?
    \A x, y, z \in S : (R[x, y] /\ R[y, z] => R[x, z])

TransitiveClosure(R) == \* Compute the transitive closure of relation R over set S.
    \A x, y \in S : (R[x, y] => \E z \in S : R[x, z] /\ R[z, y])

ReflexiveTransitiveClosure(R) == \* Compute the reflexive transitive closure of relation R over set S.
    \A x \in S : (R[x, x] /\ \E y \in S : R[x, y] => \E z \in S : R[x, z] /\ R[z, y])

IsConnected(R) == \* Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S?
    \E x, y \in S : (x \in S /\ y \in S /\ \E z \in S : R[x, z] /\ R[z, y])

=============================================================================
====