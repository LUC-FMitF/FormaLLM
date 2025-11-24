---- MODULE Relation ----

(**************************************************************************)
(* This module provides some basic operations on relations, represented    *)
(* as binary Boolean functions over some set S.                            *)
(**************************************************************************)

CONSTANTS S

VARIABLES R

IsReflexive(R) == \* Is the relation R reflexive over set S?
    \A x \in S : R[x, x]

IsIrreflexive(R) == \* Is the relation R irreflexive over set S?
    \A x \in S : \A y \in S : R[x, y] => x = y

IsSymmetric(R) == \* Is the relation R symmetric over set S?
    \A x \in S : \A y \in S : R[x, y] => R[y, x]

IsAsymmetric(R) == \* Is the relation R asymmetric over set S?
    \A x \in S : \A y \in S : R[x, y] => \NOT R[y, x]

IsTransitive(R) == \* Is the relation R transitive over set S?
    \A x \in S : \A y \in S : \A z \in S : R[x, y] /\ R[y, z] => R[x, z]

TransitiveClosure(R) == \* Compute the transitive closure of relation R over set S.
    [x \in S |-> \A y \in S : R[x, y]]

ReflexiveTransitiveClosure(R) == \* Compute the reflexive transitive closure of relation R over set S.
    [x \in S |-> \A y \in S : R[x, y] \/ R[y, x]]

IsConnected(R) == \* Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S?
    \EX x, y \in S : \EX z \in S : R[x, z] /\ R[z, y]

Spec == \* Initialize state with Init and transition with Next.
    Init /\ [](IsReflexive(R) /\ IsIrreflexive(R) /\ IsSymmetric(R) /\ IsAsymmetric(R) /\ IsTransitive(R) /\ (TransitiveClosure(R) = ReflexiveTransitiveClosure(R)) /\ IsConnected(R))
=============================================================================
====