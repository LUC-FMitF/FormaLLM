---- MODULE Relation ----

(**************************************************************************)
(* This module provides some basic operations on relations, represented    *)
(* as binary Boolean functions over some set S.                          *)
(**************************************************************************)

CONSTANTS   R,         \* The relation to operate on.
            S          \* The set of elements in the relation.
VARIABLES   x, y       \* Elements in the relation or not.
-----------------------------------------------------------------------------
R_reflexive ==    \* Is the relation R reflexive over S?                 *)
    /\ [x \in S |-> R[x,x]]

R_irreflexive ==  \* Is the relation R irreflexive over set S?            *)
    /\ ~ [x \in S |-> R[x,x]]

R_symmetric ==    \* Is the relation R symmetric over set S?             *)
    /\ [x \in S, y \in S |-> R[x,y] <=> R[y,x]]

R_asymmetric ==   \* Is the relation R asymmetric over set S?            *)
    /\ ~ [x \in S, y \in S |-> R[x,y] <=> R[y,x]]

R_transitive ==   \* Is the relation R transitive over set S?            *)
    /\ [x \in S, y \in S, z \in S |-> R[x,y] => R[y,z] => R[x,z]]

-----------------------------------------------------------------------------
R_transClosure == \* Compute the transitive closure of relation *)
    [x \in S, y \in S |-> EXISTS z \in S : R[x,z] /\ R[z,y]]

R_reflexiveTransClosure ==   \* Compute the reflexive transitive    *)
    [x \in S |-> EXISTS y \in S : R[x,y] <=> R[y,x]]             *)
(**************************************************************************)
====