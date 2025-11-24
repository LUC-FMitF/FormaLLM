---- MODULE BoyerMooreMajority 

EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS 
  EmptySeq == <<>>

VARIABLES 
  seq, cand, nextPos, count, bound == EmptySeq 

ASSUME 
  len(seq) <= MAX_LEN  (* Assuming sequence length is bounded *)

DEFINE 
  Majority(seq, v, j) == COUNT(i IN 0..j, seq[i] = v) > bound[v] 

Next == 
  /\ IF nextPos = len(seq) - 1 
  THEN EmptySeq 
  ELSE 
    [i IN 0..nextPos - 1 |-> seq[i]] 
    ++ [nextPos + 1..len(seq) - 1 |-> seq[i + 1]] 

UpdateCandidate ==
  /\ IF count > bound 
  THEN cand = seq[nextPos] 
  ELSE cand 

UpdateBound ==
  /\ IF count > bound 
  THEN bound = count 
  ELSE bound 

NextPos == 
  /\ IF count > bound 
  THEN nextPos + 1 
  ELSE nextPos 

Count == 
  /\ IF seq[nextPos] = cand 
  THEN count + 1 
  ELSE count 

Spec == 
  [len(seq) > 0] /\ Majority(seq, cand, nextPos) 
  IMPLIES cand = seq[nextPos] 

INVARIANT == 
  [len(seq) > 0] /\ Majority(seq, cand, nextPos) 
  /\ cand = seq[nextPos] 
  /\ count = COUNT(i IN 0..nextPos, seq[i] = cand) 
  /\ bound = MAX(COUNT(i IN 0..nextPos, seq[i] = v), v IN seq[0..nextPos]) 
  /\ nextPos <= len(seq) 

TLC Configuration:
CONSTANTS MAX_LEN = 1000 (* Maximum sequence length *)
SPECIFICATION Spec
INVARIANTS INVARIANT
====