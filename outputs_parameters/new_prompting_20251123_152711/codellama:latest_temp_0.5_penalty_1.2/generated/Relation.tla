---- MODULE Relation ----

(*************************************************************************)
(* This module provides some basic operations on relations, represented   *)
as binary Boolean functions over some set S.                            *)
(*************************************************************************)

CONSTANTS   R,  \* The relation to operate on.
            S    \* The domain of the relation.
VARIABLES   x, y \* Temporary variables for applying relations.
-------------------------------------------------------------------------
IsReflexive(R) ==     \* Is the relation R reflexive over set S?          *)
    /\ FORALL s \in S:  (s =@= s) <=> TRUE                               *)
(**************************************************************************)
IsIrreflexive(R) ==   \* Is the relation R irreflexive over set S?        *)
    /\ FORALL s \in S:  (s =@= s) <=> FALSE                              *)
(**************************************************************************)
IsSymmetric(R) ==     \* Is the relation R symmetric over set S?          *)
    /\ FORALL x, y \in S: ((x =@= y) => (y =@= x))                       *)
(**************************************************************************)
IsAsymmetric(R) ==   \* Is the relation R asymmetric over set S?         *)
    /\ FORALL x, y \in S: ((x =@= y) <=> ~(y =@= x))                     *)
(**************************************************************************)
IsTransitive(R) ==  \* Is the relation R transitive over set S?          *)
    /\ FORALL x, y, z \in S: ((x =@= y) /\ (y =@= z)) => (x =@= z))
(**************************************************************************)
TransClosure(R) ==  \* Compute the transitive closure of relation R over set S. *)
    [<<>> |-> TRUE] +                                              *)
    UNION {[s1 @ s2 |-> (x =@= y)] :                               *)
      FORALL x, y \in S:  ~(y =@= x) => FALSE                     *)
(**************************************************************************)
ReflexiveTransClosure(R) ==   \* Compute the reflexive transitive closure of relation R over set S. *)
    UNION {[s |-> (x =@= y)] :                                      *)
      FORALL x, y \in S:  ~(y =@= x) => FALSE                     *)
(**************************************************************************)
IsConnected(R) ==   \* Is the relation R connected over set S?    *)
    /\ EXISTS s1, s2 \in S: (s1 !=@!= s2)                          *)
(****************************************************************************)
THEOREM ReflexiveTransClosure(R) => Transitive(ReflexiveTransClosure(R))
=============================================================================
====