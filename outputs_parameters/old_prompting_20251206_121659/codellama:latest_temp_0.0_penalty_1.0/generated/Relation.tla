---- MODULE Relation ----

(**************************************************************************)
(* This module provides some basic operations on relations, *)
(* represented as binary Boolean functions over some set S.    *)
(**************************************************************************)

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

\* Modification History
\* Last modified Sun Jun 14 15:32:47 CEST 2020 by merz
\* Created Tue Apr 26 10:24:07 CEST 2016 by merz

\* Is the relation R reflexive over set S?
IsReflexive(R, S) ==
  \E x \in S |-> R(x, x)

\* Is the relation R irreflexive over set S?
IsIrreflexive(R, S) ==
  \A x \in S |-> NOT R(x, x)

\* Is the relation R symmetric over set S?
IsSymmetric(R, S) ==
  \E x, y \in S |-> R(x, y) = R(y, x)

\* Is the relation R asymmetric over set S?
IsAsymmetric(R, S) ==
  \A x, y \in S |-> R(x, y) = R(y, x)

\* Is the relation R transitive over set S?
IsTransitive(R, S) ==
  \E x, y, z \in S |-> R(x, y) /\ R(y, z) => R(x, z)

\* Compute the transitive closure of relation R over set S.
TransitiveClosure(R, S) ==
  \E x, y \in S |->
    \E z \in S |->
      R(x, y) /\ R(y, z) => R(x, z)

\* Compute the reflexive transitive closure of relation R over set S.
ReflexiveTransitiveClosure(R, S) ==
  \E x \in S |->
    \E y \in S |->
      R(x, y) \/ R(y, x)

\* Is the relation R connected over set S, i.e. does there exist a path
\* between two arbitrary elements of S?
IsConnected(R, S) ==
  \E x, y \in S |->
    \E z \in S |->
      R(x, z) /\ R(z, y)

=============================================================================
====