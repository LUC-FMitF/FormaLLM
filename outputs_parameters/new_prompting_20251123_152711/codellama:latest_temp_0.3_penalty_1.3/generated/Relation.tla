---- MODULE Relation ----

(*************************************************************************)
(* This module provides some basic operations on relations, represented  *)
(* as binary Boolean functions over some set S.                          *)
(*************************************************************************)
CONSTANTS   R,            \* The relation to operate on.
            S             \* The domain of the relation.
VARIABLES   r,             \* A copy of the input relation.
            s              \* The set of all elements in the domain.
-----------------------------------------------------------------------------
IsReflexive(R) ==    \* Is the relation R reflexive over S?                     *)
    /\ r = [s |-> TRUE]   \* A relation is reflexive if it contains a loop for  *)
    /\ s \in S            \* each element in its domain.                      *)
IsIrreflexive(R) ==  \* Is the relation R irreflexive over set S?               *)
    /\ r = [s |-> FALSE]  \* A relation is irreflexive if it does not contain   *)
    /\ s \in S            \* any loops.                                        *)
IsSymmetric(R) ==    \* Is the relation R symmetric over set S?                 *)
    /\ r = [s |-> {x, y} : x <:> y]  \* A relation is symmetric if it contains   *)
    /\ s \in S            \* a loop for each pair of elements.                  *)
IsAsymmetric(R) ==  \* Is the relation R asymmetric over set S?                *)
    /\ r = [s |-> {x, y} : x <:> NOT y]  \* A relation is asymmetric if   *)
    /\ s \in S            \* it contains a loop for each pair of elements. *)
IsTransitive(R) == \* Is the relation R transitive over set S?         *)
    /\ r = [s |-> {x, y} : x <:> z]  \* A relation is transitive if it   *)
    /\ s \in S            \* contains a loop for each triple of elements. *)
-----------------------------------------------------------------------------
TransClosure(R) ==     \* Compute the transitive closure of relation R over set S. *)
    [s |-> UNION {[x, y] : x <:> z} : r = [z |-> TRUE]]  \* The transitive closure   *)
    /\ s \in S            \* is defined as the smallest relation that contains all     *)
                          \* loops in R and all chains of length at least two.           *)
ReflexiveTransClosure(R) ==      \* Compute the reflexive transitive closure of relation R over set S. *)
    [s |-> UNION {[x, y] : x <:> z} : r = [z |-> TRUE]]  \* The reflexive transitive   *)
                              \* closure is defined as the smallest relation that contains all     *)
                              \* loops in R and all chains of length at least two.           *)
-----------------------------------------------------------------------------
THEOREM IsReflexive(R) => [](r = [s |-> TRUE])  /\ s \in S   )
=============================================================================
====