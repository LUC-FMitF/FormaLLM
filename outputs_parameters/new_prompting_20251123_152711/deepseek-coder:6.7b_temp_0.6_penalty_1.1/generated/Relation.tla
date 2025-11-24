---- MODULE Relation ----

(*********************************************************************)
(* This module provides some basic operations on relations, represented *)
(* as binary Boolean functions over some set S.                         *)
(*********************************************************************)

VARIABLES R \* The relation to be analyzed.
CONSTANTS S  \* The domain of the relation and its elements.

Reflexive == /\ [x, y] -> x = y :-> R[x, y]
Irreflexive == /\ [x] -> ~R[x, x]
Symmetric == /\ [x, y] -> R[x, y] => R[y, x]
Asymmetric == /\ [x, y] -> R[x, y] => (x = y)
Transitive == /\ [x, y, z] -> R[x, y] && R[y, z] => R[x, z]

TransClosure == [x, y] -> TransClosure'[x, y]
TransClosure'[x, y] == x = y || (/\ [z] -> R[y, z] => TransClosure'[x, z])

ReflTransClosure == [x, y] -> ReflTransClosure'[x, y]
ReflTransClosure'[x, y] == x = y || (/\ [z] -> R[y, z] => ReflTransClosure'[x, z]) && R[x, y]

Connected == /\ [x, y] -> Connected'[x, y]
Connected'[x, y] == x = y || (/\ [z] -> R[y, z] => Connected'[x, z])

=============================================================================
====
TLC Configuration:
CONSTANTS S = {1, 2, 3}
SPECIFICATION Reflexive /\ Irreflexive /\ Symmetric /\ Asymmetric /\ Transitive /\ TransClosure /\ ReflTransClosure /\ Connected
INVARIANTS S
====