---- MODULE Majority ----
EXTENDS Integer

CONSTANT Values = {0, 1} \* input sequence of values, never changes *
VARIABLE seq[Nat] /\ seq'[Nat] \* next position of sequence to be checked *
VARIABLE cand /\ cand' \* current candidate for having a majority *
VARIABLE lb /\ lb' \* lower bound for the number of occurrences of the candidate so far *

(* set of indexes in the prefix of the sequence strictly before j holding v *)
IndexesBeforeJ(v, seq[Nat], j) == {i | i < j /\ seq[i] = v} 

(* number of times v occurs in that prefix *)
PrefixCount(v, seq[Nat], j) == 0 + (1 IF Cardinality(IndexesBeforeJ(v, seq[Nat], j)) > lb ELSE 0)

(* number of times v occurs in all of the sequence *)
TotalCount(v, seq[Nat]) == Sum {PrefixCount(v, seq[Nat], j)} (j \in Nat)

Init == 1 < LENGTH seq /\ lb = 0 /\ cand = seq[0] 

Next == (cand' = IF TotalCount(cand, seq[Nat]) > Cardinality(seq[Nat])/2 - lb ELSE cand) 
        /\ (lb' = IF PrefixCount(cand, seq[Nat], LENGTH seq) > lb THEN TotalCount(cand, seq[Nat]) ELSE lb)
        /\ ((seq'[LENGTH seq] = cand') /\ TAKE(seq', 1 + LENGTH seq))

Inv == (lb \leq TotalCount(cand, seq[Nat])) /\ (TotalCount(cand, seq[Nat]) - lb > Cardinality(IndexesBeforeJ(cand, seq[Nat], LENGTH seq))) 

Spec == Init /\ [][Next]_seq Inv 

TLC Config:
CONSTANTS Values = {0,1}
SPECIFICATION Spec
INVARIANTS Inv
====