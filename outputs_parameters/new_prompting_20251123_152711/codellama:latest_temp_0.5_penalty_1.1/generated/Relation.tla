---- MODULE Relation ----

(***************************************************************************)
(* This module provides some basic operations on relations, represented  *)
as binary Boolean functions over some set S.                            *)
(***************************************************************************)

CONSTANTS   S, R                 \* The set of elements and the relation.
VARIABLES   r                    \* A binary function representing the relation.
----------------------------------------------------------------------------
IsReflexive(R) ==  \* Is the relation R reflexive over set S?
    /\ r \in [S -> S -> Bool]
    /\ \A x \in S : r[x][x] = TRUE

IsIrreflexive(R) ==  \* Is the relation R irreflexive over set S?
    /\ r \in [S -> S -> Bool]
    /\ \A x, y \in S : x /= y => r[x][y] = FALSE

IsSymmetric(R) ==    \* Is the relation R symmetric over set S?
    /\ r \in [S -> S -> Bool]
    /\ \A x, y \in S : x /= y => r[x][y] = r[y][x]

IsAsymmetric(R) ==  \* Is the relation R asymmetric over set S?
    /\ r \in [S -> S -> Bool]
    /\ \A x, y \in S : x /= y => r[x][y] = FALSE => r[y][x] = FALSE

IsTransitive(R) ==  \* Is the relation R transitive over set S?
    /\ r \in [S -> S -> Bool]
    /\ \A x, y, z \in S : x /= y /\ y /= z => r[x][y] = TRUE => r[x][z] = TRUE

TransitiveClosure(R) ==  \* Compute the transitive closure of relation R over set S.
    LET
      RECURSIVE TransitiveClosure(_, _)
      TransitiveClosure(r, x) ==
        [y |-> r[x][y] \/ TransitiveClosure(r, y)]
    IN
      [x |-> TransitiveClosure(r, x)]

ReflexiveTransitiveClosure(R) ==  \* Compute the reflexive transitive closure of relation R over set S.
    LET
      RECURSIVE ReflexiveTransitiveClosure(_, _)
      ReflexiveTransitiveClosure(r, x) ==
        [y |-> r[x][y] \/ ReflexiveTransitiveClosure(r, y)]
    IN
      [x |-> TRUE /\ ReflexiveTransitiveClosure(r, x)]

IsConnected(R) ==  \* Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S?
    /\ r \in [S -> S -> Bool]
    /\ \A x, y \in S : x /= y => \EX z \in S : x = z /\ y = z \/ R[x][z] \/ R[z][y]

=============================================================================
====