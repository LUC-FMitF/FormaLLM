---- MODULE Relation ----

(**************************************************************************)
(* This module provides some basic operations on relations, represented  *)
(* as binary Boolean functions over some set S.                         *)
(**************************************************************************)

CONSTANTS
   S,           \* The set of elements in the relation.
   R             \* The relation, a function from S x S to Bool.
VARIABLES
   r,            \* A temporary variable for the current element of S.
   s              \* A temporary variable for the current element of S.
   P,            \* A proposition variable.
   Q              \* A proposition variable.
----------------------------------------------------------------------------
IsReflexive(R) ==    \* Is the relation R reflexive over set S?
    /\ r \in S
    /\ r =^= s
    /\ R[r,s]

IsIrreflexive(R) ==  \* Is the relation R irreflexive over set S?
    /\ r \in S
    /\ NOT r =^= s
    /\ NOT R[r,s]

IsSymmetric(R) ==     \* Is the relation R symmetric over set S?
    /\ r \in S
    /\ s \in S
    /\ (R[r,s] <=> R[s,r])

IsAsymmetric(R) ==    \* Is the relation R asymmetric over set S?
    /\ r \in S
    /\ s \in S
    /\ (R[r,s] => NOT R[s,r])

IsTransitive(R) ==     \* Is the relation R transitive over set S?
    /\ r \in S
    /\ s \in S
    /\ t \in S
    /\ R[r,s]
    /\ R[s,t]
    /\ R[r,t]

TransClosure(R) ==   \* Compute the transitive closure of relation R over set S.
    [
        RECURSIVE TransClosure(_, _)
        TransClosure(s, r) ==
            IF r =^= s
            THEN TRUE
            ELSE (
                EXIST Q (TransClosure(s, Q) /\ R[Q,r])
              )
    ]

ReflexiveTransClosure(R) ==   \* Compute the reflexive transitive closure of relation R over set S.
    [
        RECURSIVE ReflexiveTransClosure(_, _)
        ReflexiveTransClosure(s, r) ==
            IF r =^= s
            THEN TRUE
            ELSE (
                EXIST Q (ReflexiveTransClosure(Q, r) /\ R[Q,s])
              )
    ]

IsConnected(R) ==     \* Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S?
    [
        RECURSIVE IsConnected(_, _)
        IsConnected(s, r) ==
            IF s =^= r
            THEN TRUE
            ELSE (
                EXIST Q (IsConnected(Q, s) /\ R[r,Q])
              )
    ]
----------------------------------------------------------------------------
THEOREM ReflexiveTransClosure(R) => [](IsReflexive(R) /\ IsTransitive(R))
=============================================================================
====