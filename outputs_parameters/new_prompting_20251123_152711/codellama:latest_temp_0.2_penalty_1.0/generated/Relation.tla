---- MODULE Relation ----

(*************************************************************************)
(* This module provides some basic operations on relations, represented  *)
as binary Boolean functions over some set S.                            *)
(*************************************************************************)

CONSTANTS   R,    \* The relation to operate on.
            S     \* The domain of the relation.
VARIABLES   x, y  \* Temporary variables for reasoning about relations.
-------------------------------------------------------------------------
IsReflexive(R) ==                                                       *)
    /\ R[x, x] = TRUE                                                   *)
(* Is the relation R reflexive over set S? *)
**************************************************************************)

IsIrreflexive(R) ==                                                     *)
    \A x \in S : NOT (R[x, x])                                          *)
(* Is the relation R irreflexive over set S? *)
**************************************************************************)

IsSymmetric(R) ==                                                       *)
    /\ (\A x, y \in S : R[x, y] = R[y, x])                              *)
(* Is the relation R symmetric over set S? *)
**************************************************************************)

IsAsymmetric(R) ==                                                      *)
    /\ (\A x, y \in S : NOT (R[x, y] = R[y, x]))                        *)
(* Is the relation R asymmetric over set S? *)
**************************************************************************)

IsTransitive(R) ==                                                      *)
    /\ (\A x, y, z \in S : R[x, y] = TRUE => R[y, z] = TRUE)  *)
(* Is the relation R transitive over set S? *)
**************************************************************************)

TransClosure(R) ==                                                *)
    [x, y \in S |-> R[x, y]]                                        *)
(* Compute the transitive closure of relation R over set S.      *)
**************************************************************************)

ReflexiveTransClosure(R) ==                                         *)
    [x, x \in S |-> TRUE] @@ TransClosure(R)                        *)
(* Compute the reflexive transitive closure of relation R over set*)
(* S.                                                                *)
**************************************************************************)

IsConnected(R) ==                                                    *)
    /\ (\A x, y \in S : EXISTS z \in S : R[x, z] = TRUE =>          *)
        EXISTS z' \in S : R[z', y] = TRUE)                            *)
(* Is the relation R connected over set S? *)
**************************************************************************)

IsReflexive(R) /\ IsSymmetric(R) ==> IsTransitive(R)                *)
(* If a relation is reflexive and symmetric, it must be transitive.  *)
**************************************************************************)

IsIrreflexive(R) \/ IsAsymmetric(R) ==> NOT (IsConnected(R))         *)
(* If a relation is irreflexive or asymmetric, it cannot be connected.*)
**************************************************************************)
====