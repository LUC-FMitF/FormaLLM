---- MODULE Relation ----
EXTENDS FiniteSets, Naturals, Sequences, ZSequences

CONSTANTS SetS = {0, 1} (* The set of all elements *)

(* A binary relation R over a set S is represented as a function from S to S to Boolean. *)
TYPE Relation = [SetS -> SetS] -> BOOLEAN

(* Is the relation R reflexive over S? *)
Reflexive(R, S) == \A x : S : R[x][x] (* For all x in S, R(x,x) is true. *)

(* Is the relation R irreflexive over set S? *)
Irreflexive(R, S) == \E x : S : ~R[x][x] (* There exists an x in S such that R(x,x) is false. *)

(* Is the relation R symmetric over set S? *)
Symmetric(R, S) == \A x, y : S : R[x][y] => R[y][x] (* For all x and y in S, if R(x,y) is true then R(y,x) is also true. *)

(* Is the relation R asymmetric over set S? *)
Asymmetric(R, S) == \A x, y : S : R[x][y] => ~R[y][x] (* For all x and y in S, if R(x,y) is true then R(y,x) is false. *)

(* Is the relation R transitive over set S? *)
Transitive(R, S) == \A x, y, z : S : R[x][y] && R[y][z] => R[x][z] (* For all x, y and z in S, if R(x,y) is true and R(y,z) is also true then R(x,z) is also true. *)

(* Compute the transitive closure of relation R over set S. *)
TransClosure(R, S) == [s1, s2 : SetS |-> R[s1][s2] \/ (\E s3 : S : R[s1][s3] && TransClosure(R, S)[s3][s2])] (* The relation is extended by the rule that if there exists a path from x to y and z then it also extends to paths of length 2. *)

(* Compute the reflexive transitive closure of relation R over set S. *)
ReflTransClosure(R, S) == [s1, s2 : SetS |-> R[s1][s2] \/ (\E s3 : S : ReflTransClosure(R, S)[s1][s3] && R[s3][s2])] (* The relation is extended by the rule that if there exists a path from x to y and z then it also extends to paths of length 2. *)

(* Is the relation R connected over set S, i.e. does there exist a path between two arbitrary elements of S? *)
Connected(R, S) == \A x, y : S : (\E z : S : R[x][z] && R[z][y]) (* For all pairs (x,y) in S, there exists an element z such that both R(x,z) and R(z,y) are true. *)

(* TLC Configuration *)
CONSTANTS 
  SetS = {0, 1}
  
SPECIFICATION 
  [s : SetS |-> Reflexive[R][s] /\ Irreflexive[R][s] /\ Symmetric[R][s] /\ Asymmetric[R][s] /\ Transitive[R][s]]
  
INVARIANTS 
  (Connected[R][s1][s2]) = ((\E s3 : SetS : R[s1][s3] && R[s3][s2]))
=============================================================================
====