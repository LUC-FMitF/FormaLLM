---- MODULE Relation ----

(***************************************************************************)
(* This module provides some basic operations on relations, represented     *)
(* as binary Boolean functions over some set S.                             *)
(*                                                                         *)
(* Is the relation R reflexive over S?                                      *)
(*                                                                         *)
(* Is the relation R irreflexive over set S?                                *)
(*                                                                         *)
(* Is the relation R symmetric over set S?                                  *)
(*                                                                         *)
(* Is the relation R asymmetric over set S?                                 *)
(*                                                                         *)
(* Is the relation R transitive over set S?                                 *)
(*                                                                         *)
(* Compute the transitive closure of relation R over set S.                 *)
(*                                                                         *)
(* Compute the reflexive transitive closure of relation R over set S.       *)
(*                                                                         *)
(* Is the relation R connected over set S, i.e. does there exist a path     *)
(* between two arbitrary elements of S?                                     *)
(***************************************************************************)

CONSTANTS
  EmptySet == {}
  OneElementSet == {0}

VARIABLES
  R, S <<>>

\* Is the relation R reflexive over S?
Reflexive[R, S] == !EXISTS x \in S : ~(x -> x IN DOMAIN R)

\* Is the relation R irreflexive over set S?
Irreflexive[R, S] == !EXISTS x \in S : (x -> x IN DOMAIN R)

\* Is the relation R symmetric over set S?
Symmetric[R, S] == !EXISTS {a, b} \in POWERSET S /\ a != b : ~(b -> a IN DOMAIN R) OR (a -> b NOTIN DOMAIN R)

\* Is the relation R asymmetric over set S?
Asymmetric[R, S] == !EXISTS {a, b} \in POWERSET S /\ a != b : ~(b -> a IN DOMAIN R) AND (a -> b IN DOMAIN R)

\* Is the relation R transitive over set S?
Transitive[R, S] == !EXISTS {a, b, c} \in POWERSET S /\ a != b != c : ~(b -> a IN DOMAIN R) AND (a -> c IN DOMAIN R) IMPLIES (b -> c IN DOMAIN R)

\* Compute the transitive closure of relation R over set S.
TransClosure[R, S] == UNION {X : X \subseteq POWERSET S /\ Cardinality(X) > 0} [{x, y} \in X -> (y IN DOMAIN R[x]) IMPLIES (X =< {z | z IN DOMAIN R[y]} <: Y & Y != EmptySet)]

\* Compute the reflexive transitive closure of relation R over set S.
ReflexiveTransClosure[R, S] == UNION {X : X \subseteq POWERSET S /\ Cardinality(X) > 0} [{x, y} \in X -> (y IN DOMAIN R[x]) IMPLIES (X =< {z | z IN DOMAIN R[y]} <: Y & Y != EmptySet)] UNION {x : x \in S}

\* Is the relation R connected over set S, i.e. does there exist a path     *)
(* between two arbitrary elements of S?                                     *)
Connected[R, S] == FORALL {a, b} \in POWERSET S /\ a != b : EXISTS X \subseteq POWERSET S /\ Cardinality(X) > 0 : (a IN DOMAIN R[b]) OR ((EXISTS x \in X : ~(x -> a NOTIN DOMAIN R[b])) AND (X =< {z | z IN DOMAIN R[y]} <: Y & Y != EmptySet))

SPECIFICATION Spec == [](Reflexive[R, S] /\ Transitive[R, S]) IMPLIES Connected[R, S]

INVARIANTS Inv == ([](Reflexive[R, S] /\ Transitive[R, S]))

TLC Configuration:
CONSTANTS 
  EmptySet = {}
  OneElementSet = {0}
SPECIFICATION Spec
INVARIANTS Inv
====