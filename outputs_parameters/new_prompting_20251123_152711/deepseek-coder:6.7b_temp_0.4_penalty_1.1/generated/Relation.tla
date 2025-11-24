---- MODULE Relation ----

(***************************************************************************
This module provides some basic operations on relations, represented    
as binary Boolean functions over some set S.                            
***************************************************************************)

CONSTANTS   S \* The set of all elements.
VARIABLES   R \* The relation between two elements in S.

Reflexive == --------> EXISTS x : S [R(x, x)]
Irreflexive == -----> NOT EXISTS x : S [R(x, x)]
Symmetric == ---------> EXISTS {x, y} : S [R(x, y) => R(y, x)]
Asymmetric == --------> EXISTS {x, y} : S [R(x, y) AND NOT R(y, x)]
Transitive == --------> EXISTS {x, y, z} : S [R(x, y) AND R(y, z)]

\* Compute the transitive closure of relation R over set S.
TransClosure == UNION {{x, y} : S [R(x, y)]}

\* Compute the reflexive transitive closure of relation R over set S.
ReflTransClosure == TRANSITIVE_CLOSE {R}

Connected == -----------> EXISTS {u, v} : S [EXISTS (w:S) [Path(u, w, v)]]
  WHERE Path(x, y, z) == x = y OR EXISTS w : S [Path(y, w, z)] AND R(y, w)

Specification == -----> [] Reflexive /\ Irreflexive /\ Symmetric /\ Asymmetric /\ Transitive 
                     /\ [] Connected
===============================================================================
====

TLC Configuration:
CONSTANTS  S = {1,2,3}
SPECIFICATION Spec
INVARIANTS Reflexive /\ Irreflexive /\ Symmetric /\ Asymmetric /\ Transitive 
                     /\ Connected
====