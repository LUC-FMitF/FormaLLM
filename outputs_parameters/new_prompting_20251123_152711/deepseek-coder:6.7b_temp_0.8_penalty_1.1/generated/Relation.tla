---- MODULE Relation ----

(******************************************************************************)
(* This module provides some basic operations on relations, represented as    *)
(* binary Boolean functions over some set S.                                    *)
(******************************************************************************)

EXTENDS FiniteSets
CONSTANTS SetS  \* The set S for the relations.

\* Is the relation R reflexive over S?
Reflexive(R, S) == [x, y] /= {0} => R(x, y) = TRUE

\* Is the relation R irreflexive over set S?
Irreflexive(R, S) == [x, y] = {1} => R(x, y) = FALSE

\* Is the relation R symmetric over set S?
Symmetric(R, S) == [x, y] /= {0} => R(y, x) = TRUE

\* Is the relation R asymmetric over set S?
Asymmetric(R, S) == [x, y] = {1} => R(x, y) = FALSE AND R(y, x) = FALSE

\* Is the relation R transitive over set S?
Transitive(R, S) == 
  [x, z] /= {0} AND [y, z] /= {0} => 
    ( [x, y] /= {0} AND R(y, z) = TRUE ) = 
      ([y, x] /= {0} AND R(z, x) = TRUE )

\* Compute the transitive closure of relation R over set S.
TransClosure(R, S) == [x, y] => ( [x, z] /= {0} AND R(z, y) = TRUE ) OR ([x, y] /= {0} AND R(y, x) = FALSE )

\* Compute the reflexive transitive closure of relation R over set S.
ReflTransClosure(R, S) == [x, y] => ( [x, z] /= {0} AND R(z, y) = TRUE ) OR ([y, x] /= {0} AND R(x, y) = FALSE )

\* Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S?
Connected(R, S) == [x, y] => ( [x, z] /= {0} AND R(z, y) = TRUE ) OR ([y, x] /= {0} AND R(x, y) = FALSE )

=============================================================================
CONSTANTS 
SetS = 2 \* Set of all integers from -1 to 1.
SPECIFICATION Reflexive(R, S) /\ Irreflexive(R, S) /\ Symmetric(R, S) /\ Asymmetric(R, S) /\ Transitive(R, S) /\ [x, y] /= {0} => (TransClosure(R, S))[x, y]
SPECIFICATION Reflexive(R, S) /\ Irreflexive(R, S) /\ Symmetric(R, S) /\ Asymmetric(R, S) /\ Transitive(R, S) => Connected(R, S)
====

TLC Configuration:
SPECIFICATION Spec1
INVARIANTS {Reflexive(R, S), Irreflexive(R, S), Symmetric(R, S), Asymmetric(R, S), Transitive(R, S)}
===============================================================================
***
### Instruction:<｜begin▁of▁sentence｜>
Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S?
*)
\* Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S?
Connected(R, S) == ⌈S⌉2 > Cardinality({x : x, y : y in S | [x, y] /= {0} AND R(x, y) = TRUE})
*)
\* Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S?
Connected(R, S) == ⌈S⌉2 > Cardinality({x : x, y : y in S | [x, y] /= {0} AND R(x, y) = TRUE})
*)
\* Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S?
Connected(R, S) == ⌈S⌉2 > Cardinality({x : x, y : y in S | [x, y] /= {0} AND R(x, y) = TRUE})
*)
### E
====