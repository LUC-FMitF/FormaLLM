---- MODULE Majority ----

(***************************************************************************)
(* TLA+ specification and proof of the majority vote algorithm due to Boyer *)
(* and Moore.                                                                *)
(* R.S. Boyer, J.S. Moore: MJRTY - A Fast Majority Vote Algorithm.           *)
(* In: R.S. Boyer (ed.): Automated Reasoning: Essays in Honor of Woody       *)
(* Bledsoe, pp. 105-117. Dordrecht, The Netherlands, 1991.                   *)
(* Originally published in a technical report from 1981.                     *)
(* The algorithm takes as input a sequence of values, makes one pass over    *)
(* the sequence, and reports an element cand such that no element other      *)
(* than cand may have an absolute majority in the sequence.                  *)
(***************************************************************************)
Although seq is an input to the algorithm, we make it a variable so that 
we can use the model checker to verify the algorithm for all sequences   
up to some bounded size.                                                  *)
(***************************************************************************)
(***************************************************************************)
(* Definitions used for stating correctness.                                 *)
(***************************************************************************)

CONSTANTS
  EmptySet == {}
  OneSet == {1}
  
VARIABLES
  +seq \in Seq(\{0, 1\}) (* input sequence of values, never changes *)
  -pos \in Range(0, Len(seq)+1) (* next position of sequence to be checked *)
  +cand \in \{0, 1\} (* current candidate for having a majority *)
  -lower \in Range(0, pos+1) (* lower bound for the number of occurrences of the candidate so far *)
  
(* set of indexes in the prefix of the sequence strictly before j holding v *)
F_IndexesInPrefix(v, j) == {i | i \in 0..j-1 /\ seq[i] = v}

(* number of times v occurs in that prefix *)
F_CountInPrefix(v) == Cardinality(F_IndexesInPrefix(v, pos))

(* number of times v occurs in all of the sequence *)
F_TotalCount(v) == F_CountInPrefix(v) + IF pos = Len(seq) THEN 0 ELSE seq[pos] ENDIF

INVARIANT
  +-Inv /\ -Inv ==> [][](cand \in \{0, 1\} /\ lower > 0 /\ (F_TotalCount(cand) > F_TotalCount(\{0, 1\} - cand)))
  
NEXTSTATE
  +-NextState == IF pos = Len(seq) THEN EmptySet ELSE {pos + 1} ENDIF
  -NextState == IF pos = Len(seq) THEN EmptySet ELSE (IF seq[pos] = cand THEN lower ELSE F_CountInPrefix(cand) + 1) ENDIF
  
SPECIFICATION
  +[](Len(seq) = 0 \/ EXISTS {i | i \in 0..Len(seq)-1 /\ (F_TotalCount(\{0, 1\} - seq[i]) > F_TotalCount(seq[i]))})
  
TLC Configuration:
CONSTANTS
  +len == 2 (* length of sequence *)
  +seq == [0, 1, 0, 1, 0] (* example input sequence *)
====