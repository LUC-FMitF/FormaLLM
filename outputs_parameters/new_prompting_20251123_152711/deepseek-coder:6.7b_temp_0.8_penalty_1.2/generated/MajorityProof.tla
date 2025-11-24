---- MODULE MajorityProof ----

(**************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of  *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ... , n-1}).                                             *)
(**************************************************************************)

CONSTANTS EmptyZSeq = <<>> \* The empty zero-indexed sequence

OPERATION ZIndices(s) == IF s = EmptyZSeq THEN {} ELSE DOMAIN s \* The set of valid indices for zero-indexed sequence s

OPERATION ZSeqOfLength(S, n) == 
  IF n = 0 
  THEN {EmptyZSeq} 
  ELSE [i \in 0..n - 1 |-> S] \* The set of all zero-indexed sequences of elements in S with length n

OPERATION ZSeq(S) == UNION {ZSeqOfLength(S, n): n IN Naturals} \* The set of all zero-indexed sequences of elements in S

OPERATION ZLen(s) == 
  IF s = EmptyZSeq 
  THEN 0 
  ELSE CARDINALITY DOMAIN s \* The length of zero-indexed sequence s

OPERATION ZSeqFromSeq(seq) ==
  IF seq = EmptyZSeq 
  THEN EmptyZSeq 
  ELSE [i IN 0..CARDINALITY DOMAIN seq - 1 |-> seq[i + 1]] \* Converts from a one-indexed sequence to a zero-indexed sequence

OPERATION SeqFromZSeq(zseq) == 
  IF zseq = EmptyZSeq 
  THEN <<>> 
  ELSE [i IN 1..CARDINALITY DOMAIN zseq |-> zseq[i - 1]] \* Converts from a zero-indexed sequence to a one-indexed sequence

OPERATION Rotation(s, r) == 
  IF s = EmptyZSeq 
  THEN EmptyZSeq 
  ELSE [i IN ZIndices(s) |-> s[(i + r) MOD CARDINALITY DOMAIN s]] \* Rotate the string s to the left by r indices

OPERATION Rotations(s) == 
  IF s = EmptyZSeq 
  THEN {} 
  ELSE {[shift IN ZIndices(s), seq IN CARDINALITY DOMAIN s |-> Rotation(s, shift)]} \* The set of all rotations of zero-indexed sequence s

CONSTANTS EmptyString = <<>>

LEMMA ZSeqOfLengthIncludesEmptyZSeq == 
  [i IN 0..n - 1 |-> S] = EmptyZSeq IMPLIES n = 0 \* Auxiliary lemmas about positions and occurrences.

LEMMA RotationWorksAsExpected ==
  [i IN ZIndices(s) |-> s[(i + r) MOD CARDINALITY DOMAIN s]] = EmptyZSeq IFF s = EmptyZSeq \* Auxiliary lemmas about positions and occurrences.

LEMMA SeqFromZSeqWorksAsExpected == [i IN 1..CARDINALITY DOMAIN zseq |-> zseq[i - 1]] = <<>> IFF zseq = EmptyZSeq \* Auxiliary lemmas about positions and occurrences.

LEMMA ZIndicesWorksAsExpected == [i IN 0..n - 1] = {} IFF n = 0 \* Auxiliary lemmas about positions and occurrences.

LEMMA RotationsWorksAsExpected == 
  {[shift IN ZIndices(s), seq IN CARDINALITY DOMAIN s |-> Rotation(s, shift)]} = {} IFF s = EmptyZSeq \* Auxiliary lemmas about positions and occurrences.

LEMMA ZLenWorksAsExpected == 0 = CARDINALITY DOMAIN s IFf s = EmptyZSeq \* Auxiliary lemmas about positions and occurrences.

LEMMA ZSeqFromSeqWorksAsExpected == [i IN 0..CARDINALITY DOMAIN seq - 1 |-> seq[i + 1]] = <<>> IFF seq = EmptyZSeq \* Auxiliary lemmas about positions and occurrences.

LEMMA ZSeqWorksAsExpected == UNION {[i IN 0..n |-> S]: n IN Naturals} = {} IFf S = EmptySet \* Auxiliary lemmas about positions and occurrences.

INVARIANT InvZSequences(s) == 
   CARDINALITY DOMAIN s = ZLen(s) 
   /\ [i IN 0..CARDINALITY DOMAIN s - 1 |-> s[i] ELEM S] \* We prove correctness based on the inductive invariant.
=============================================================================
TLC configuration
------------------------
CONSTANTS Naturals = {0, 1, ...}
SPECIFICATION InvZSequences(s)
INVARIANTS InvZSequences(s)
====
**************************************************************************)
The proofs of lemmas about positions and occurrences are left as exercises. They essentially involve manipulating the indices to show that certain properties hold true for all elements in the sequences. 

For instance, ZLenWorksAsExpected shows that if a zero-indexed sequence s is empty (i.e., its length is zero), then the set of valid indices for s should also be empty. This can be extended for other lemmas as well.

Finally, we have an inductive invariant InvZSequences(s) which states that a zero-indexed sequence's length matches its cardinality and every element in the sequence belongs to the set S. The correctness of our model is then established by proving that this invariant holds true at all possible states of our system (i.e., for each zero-indexed sequence s).
====