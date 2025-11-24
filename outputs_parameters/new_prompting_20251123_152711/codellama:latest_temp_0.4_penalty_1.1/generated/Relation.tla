---- MODULE Relation ----

(**************************************************************************)
(* This module provides some basic operations on relations, represented   *)
(* as binary Boolean functions over some set S.                            *)
(**************************************************************************)

CONSTANTS    S     \* The set of elements in the relation.
VARIABLES    R     \* The relation.

IsReflexive ==  \* Is the relation R reflexive over set S?
    /\ R = [s \in S |-> s]

IsIrreflexive == \* Is the relation R irreflexive over set S?
    /\ \A s \in S : R[s] = FALSE

IsSymmetric ==  \* Is the relation R symmetric over set S?
    /\ \A s1, s2 \in S : s1 \neq s2 => R[s1] \/ R[s2] => R[s1] = R[s2]

IsAsymmetric == \* Is the relation R asymmetric over set S?
    /\ \A s1, s2 \in S : s1 \neq s2 => R[s1] => ~R[s2]

IsTransitive ==  \* Is the relation R transitive over set S?
    /\ \A s1, s2, s3 \in S : s1 \neq s2 /\ s2 \neq s3 => R[s1] /\ R[s2] => R[s1] \/ R[s3]

TransClosure ==  \* Compute the transitive closure of relation R over set S.
    [s \in S |->
      IF s = EmptySet
      THEN FALSE
      ELSE ~(R \setminus {s}) @@ s
    ]

ReflexiveTransClosure ==  \* Compute the reflexive transitive closure of relation R over set S.
    [s \in S |->
      IF s = EmptySet
      THEN FALSE
      ELSE ~(R \setminus {s}) @@ (s \union {s})
    ]

IsConnected ==  \* Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S?
    /\ \A s1, s2 \in S : s1 \neq s2 => ? [s \in S |-> R[s]]

=============================================================================
====