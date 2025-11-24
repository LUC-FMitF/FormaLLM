---- MODULE Relation ----
EXTENDS FiniteSets, Naturals, Sequences, ZSequences

CONSTANTS 
  EmptyRel == [x, y |-> FALSE]

VARIABLES 
  R, S, T

(* Basic operations on relations *)
Reflexive(R, S) == [x, y |-> R[x, y] \/ x = y]
Irreflexive(R, S) == [x, y |-> NOT (R[x, y] \/ x = y)]
Symmetric(R, S) == [x, y |-> R[x, y] IMPLIES x = y]
Asymmetric(R, S) == [x, y |-> R[x, y] IMPLIES x = y]
Transitive(R, S) == [x, y |-> R[x, y] AND [z |-> R[y, z]]]

(* Compute the transitive closure of a relation *)
TransClosure(R, S) == [x, y |-> EXISTS {z |-> R[x, z] AND R[z, y]}]

(* Compute the reflexive transitive closure of a relation *)
ReflTransClosure(R, S) == [x, y |-> EXISTS {z |-> (R[x, z] OR x = z) AND R[z, y]}]

(* Check if a relation is connected *)
Connected(R, S) == [x, y |-> EXISTS {z |-> (R[x, z] OR R[z, y]) AND (x = z OR y = z)}]

SPECIFICATION 
  (* A relation is reflexive if it contains all its own elements *)
  [] Reflexive(R, S) => FORALL {x |-> x \in S} R[x, x]
  (* A relation is irreflexive if it does not contain any of its own elements *)
  [] Irreflexive(R, S) => FORALL {x |-> x \in S} NOT R[x, x]
  (* A relation is symmetric if it is related to its inverse *)
  [] Symmetric(R, S) => FORALL {x, y |-> (x, y) \in R} R[y, x]
  (* A relation is asymmetric if it is not related to its inverse *)
  [] Asymmetric(R, S) => FORALL {x, y |-> (x, y) \in R} NOT R[y, x]
  (* A relation is transitive if it relates any two elements to their third *)
  [] Transitive(R, S) => FORALL {x, y, z |-> (x, y) \in R AND (y, z) \in R} (x, z) \in R
  (* The transitive closure of a relation contains all elements that are related *)
  [] TransClosure(R, S) => FORALL {x, y |-> (x, y) \in R OR (x, y) \in TransClosure(R, S)} R[x, y]
  (* The reflexive transitive closure of a relation contains all elements that are related *)
  [] ReflTransClosure(R, S) => FORALL {x, y |-> (x, y) \in R OR (x, y) \in ReflTransClosure(R, S)} R[x, y]
  (* A relation is connected if there exists a path between any two elements *)
  [] Connected(R, S) => FORALL {x, y |-> x \in S AND y \in S} EXISTS {z |-> (x, z) \in ReflTransClosure(R, S) AND (z, y) \in ReflTransClosure(R, S)}

INVARIANTS 
  (* A relation cannot be both symmetric and asymmetric *)
  [] NOT (Symmetric(R, S) AND Asymmetric(R, S))
  (* A relation cannot be both transitive and irreflexive *)
  [] NOT (Transitive(R, S) AND Irreflexive(R, S))
  (* The transitive closure of a relation is a subset of the original relation *)
  [] Subset(TransClosure(R, S), R)
  (* The reflexive transitive closure of a relation is a subset of the original relation *)
  [] Subset(ReflTransClosure(R, S), R)
  (* A relation is connected if and only if its transitive closure is reflexive *)
  [] Connected(R, S) IFF Subset(ReflTransClosure(R, S), R)

====