---- MODULE Relation ----

(***************************************************************************)
(* This module provides some basic operations on relations, represented     *)
(* as binary Boolean functions over some set S.                             *)
(***************************************************************************)

VARIABLES   S, R

Reflexive 
    == \A x \in S : R(x, x)

Irreflexive 
    == \A x \in S : ~R(x, x)

Symmetric 
    == \A x, y \in S : R(x, y) => R(y, x)

Asymmetric 
    == \A x, y \in S : R(x, y) /\ ~R(y, x) => x = y

Transitive 
    == \A x, y, z \in S : R(x, y) /\ R(y, z) => R(x, z)

TransitiveClosure 
    == \A x, y \in S : R(x, y) \/ (\A z \in S : R(x, z) /\ R(z, y))

ReflexiveTransitiveClosure 
    == \A x, y \in S : R(x, y) \/ (\A z \in S : R(x, z) /\ R(z, y) /\ (\A w \in S : R(z, w) => R(y, w)))

Connected 
    == \A x, y \in S : (\A z \in S : R(x, z) /\ R(z, y))

Spec 
    == [] (Reflexive /\ Irreflexive /\ Symmetric /\ Asymmetric /\ Transitive /\ 
           TransitiveClosure = R /\ ReflexiveTransitiveClosure = R /\ Connected)

INVARIANTS Reflexive /\ Irreflexive /\ Symmetric /\ Asymmetric /\ Transitive /\ 
           TransitiveClosure = R /\ ReflexiveTransitiveClosure = R /\ Connected

TLC Configuration:
CONSTANTS  S = {1,2,3}
SPECIFICATION Spec
INVARIANTS Reflexive /\ Irreflexive /\ Symmetric /\ Asymmetric /\ Transitive /\ 
           TransitiveClosure = R /\ ReflexiveTransitiveClosure = R /\ Connected
=============================================================================
====