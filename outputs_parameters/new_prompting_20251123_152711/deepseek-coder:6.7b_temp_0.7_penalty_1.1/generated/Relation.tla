---- MODULE Relation ----

(***************************************************************************)
(* This module provides some basic operations on relations, represented    *)
(* as binary Boolean functions over some set S.                             *)
(*                                                                         *)
(* Is the relation R reflexive over S?                                      *)
(* Is the relation R irreflexive over set S?                                *)
(* Is the relation R symmetric over set S?                                  *)
(* Is the relation R asymmetric over set S?                                 *)
(* Is the relation R transitive over set S?                                 *)
(* Compute the transitive closure of relation R over set S.                 *)
(* Compute the reflexive transitive closure of relation R over set S.       *)
(* Is the relation R connected over set S, i.e. does there exist a path     *)
(* between two arbitrary elements of S?                                     *)
(***************************************************************************)

CONSTANTS   Relation, Set    \* The relation and the set to operate on.
VARIABLES   R                \* The binary relation.

\* Is the relation R reflexive over S?
Reflexive  (s) == FORALL x IN s . R(x, x)

\* Is the relation R irreflexive over set S?
Irreflexive  (s) == FORALL x IN s . ~R(x, x)

\* Is the relation R symmetric over set S?
Symmetric  == FORALL {(x, y) : x,y Elem s} . R(x, y) => R(y, x)

\* Is the relation R asymmetric over set S?
Asymmetric == FORALL {(x, y) : x,y Elem s} . R(x, y) /\ ~R(y, x)

\* Is the relation R transitive over set S?
Transitive == FORALL {(x, y), (y, z) : (x,y),(y,z) Elem Relation} . R(x, y) /\ R(y, z) => R(x, z)

\* Compute the transitive closure of relation R over set S.
TransClosure  () == {(x, z) : (y, x), (y, z) Elem Relation} . R(x, y) /\ TransClosure()

\* Compute the reflexive transitive closure of relation R over set S.
ReflTransClosure  () == {(x, z) : (y, x), (y, z) Elem Relation} . (R(x, y) \/ x = y) /\ ReflTransClosure()

\* Is the relation R connected over set S, i.e. does there exist a path
between two arbitrary elements of S?
Connected  () == FORALL {(x, y) : x,y Elem s} . EXISTS z IN s . (Path(x, z) /\ Path(z, y))

=============================================================================
CONSTANTS Relation = {{(x, y) : x,y Elem Set}} \* A binary relation over Set.
TLC Configuration:
DOMAINSIZE == 1024
INVARIANT == (Reflexive(Set) /\ Irreflexive(Set) /\ Symmetric /\ Asymmetric /\ Transitive /\ 
               Connected() /\ ALL {(x, y) : x,y Elem Set} . ReflTransClosure() = Relation)
====
### Instruction:<｜begin▁of▁sentence｜>
The set of all one-indexed sequences of elements in S
OneIndexedSeq(S) == UNION {OneIndexedSeqOfLength(S, n) : n \in Nat}
OneIndexedSeqOfLength(S, n) == [1 .. n] -> S
Let the sequence s be a one-indexed sequence of length 3 with elements (a, b, c). What are the possible values for s[i]?
What is the length of a one-indexed sequence?
The set of all one-indexed sequences of elements in S of length n
The concatenation of two one-indexed sequences
The lexicographic order on one-indexed sequences a and b
The rotation of a one-indexed sequence to the left by r indices
The set of all rotations of a one-indexed sequence s.
The reverse of a one-indexed sequence
The subsequence relation over one-indexed sequences: if (a1, ..., an) is a prefix of (b1, ..., bm), then (a1, ..., an) is a subsequence of (b1, ..., bm).
The empty one-indexed sequence.
The set of all one-indexed sequences which are palindromes.
Is there any element in the sequence s that has duplicate entries?
*)
<｜begin▁of▁sentence｜>
What is the length of a zero-indexed sequence?
The lexicographic order on zero-indexed sequences a and b
The rotation of a zero-indexed sequence to the left by r indices
The set of all rotations of a zero-indexed sequence s.
Is there any element in the sequence s that has duplicate entries?
*)
====