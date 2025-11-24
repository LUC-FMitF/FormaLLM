---- MODULE Relation ----

(*************************************************************************)
(* This module provides some basic operations on relations, represented  *)
as binary Boolean functions over some set S.                            *)
(*************************************************************************)

CONSTANTS   R,    \* The relation to operate on.
            S     \* The set of elements in the relation.
VARIABLES   r,    \* A function representing the relation.
            s     \* An element from the set S.
-------------------------------------------------------------------------
IsReflexive(R) ==  \* Is the relation R reflexive over set S?           *)
    /\ ![s \in S |-> r : r[s, s]]                                       *)
    
IsIrreflexive(R) ==   \* Is the relation R irreflexive over set S?      *)
    /\ [s \in S |-> r : NOT r[s, s]]                                    *)
    
IsSymmetric(R) ==  \* Is the relation R symmetric over set S?          *)
    /\ ![s1, s2 \in S |-> r : (r[s1, s2] <=> r[s2, s1])]                *)
    
IsAsymmetric(R) ==   \* Is the relation R asymmetric over set S?       *)
    /\ [s1, s2 \in S |-> r : NOT (r[s1, s2] <=> r[s2, s1])]             *)
    
IsTransitive(R) ==  \* Is the relation R transitive over set S?        *)
    /\ ![s1, s2, s3 \in S |-> r : (r[s1, s2] AND r[s2, s3]) => r[s1, s3]]   *)
    
TransClosure(R) ==  \* Compute the transitive closure of relation R over set S.    *)
    [s1, s2 \in S |-> r : (r[s1, s2] OR EXISTS s3 \in S: r[s1, s3] AND r[s3, s2])]   *)
    
ReflexiveTransClosure(R) ==  \* Compute the reflexive transitive closure of relation R over set S.    *)
    [s \in S |-> r : (r[s, s] OR EXISTS s1 \in S: r[s, s1] AND ReflexiveTransClosure(R)[s1, s])]   *)
    
IsConnected(R) ==  \* Is the relation R connected over set S?    *)
    /\ !EXISTS s1, s2 \in S: r[s1, s2] AND NOT EXISTS s3 \in S: r[s3, s1]]   *)
    
Spec == [](IsReflexive(R) /\ IsIrreflexive(R) /\ IsSymmetric(R) /\ IsAsymmetric(R) /\ IsTransitive(R) /\ TransClosure(R) /\ ReflexiveTransClosure(R) /\ IsConnected(R))
=============================================================================
====