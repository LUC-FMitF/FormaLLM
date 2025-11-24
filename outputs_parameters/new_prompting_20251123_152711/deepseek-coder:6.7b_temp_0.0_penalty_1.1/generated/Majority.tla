---- MODULE Majority ------------------------
CONSTANTS  EmptySet, ValueType, MaxSequenceSize
VARIABLES seq[0..MaxSequenceSize], cand, j, lb

Init == \* Initialize the sequence and candidate.
    /\ seq = [i \in 0 .. (j-1) |-> EmptySet]
    /\ cand = EmptySet
    /\ j = 0
    /\ lb = 0

Next == \* The next state relation.
   /\ IF j < MaxSequenceSize THEN 
        /\ seq'[j] = seq[j] U {seq[j+1]}
        /\ cand' = IF (Cardinality(seq'[j]) - lb > Cardinality(cand)) THEN seq'[j] ELSE cand
        /\ j' = j + 1
        /\ lb' = IF (seq'[j] = cand) THEN lb + Count(seq, cand) ELSE lb
      ELSE 
        /\ seq' = seq
        /\ cand' = cand
        /\ j' = j
        /\ lb' = lb

Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<seq, cand, j, lb>>

THEOREM Spec => cand is the only value that has a majority in seq
=============================================================================
Inductive Invariant: 
For all i < j, we have Cardinality(cand) > i /\ Count(seq[0..j], cand) > 2 * (j - i)
=======================================================================================
This invariant is used to prove the correctness of the algorithm. It states that if a candidate has been found at some index 'i', it will always be the one with the majority after that, and no other value can have more than half the remaining elements in the sequence. 

The inductive step for this invariant is as follows:
Suppose the invariant holds true for all indices up to 'j'. We need to prove that it also holds for index 'j+1'.

By definition of Next, we know that seq'[j] = seq[j] U {seq[j+1]} and cand' = IF (Cardinality(seq'[j]) - lb > Cardinality(cand)) THEN seq'[j] ELSE cand.
Also, by the definition of Next, we know that j' = j + 1 and lb' = IF (seq'[j] = cand) THEN lb + Count(seq, cand) ELSE lb.

From these definitions, we can see that if seq'[j] is not equal to cand', then the invariant still holds true for all indices up to 'j+1'. 
On the other hand, if seq'[j] = cand', then we have Cardinality(cand) > j /\ Count(seq[0..j], cand) > 2 * (j - j). This is because lb' = lb + Count(seq, cand), and Count(seq, cand) is the number of times cand appears in seq.

Therefore, by the transitive property of the subset relation, we have proved that for all 'j', the invariant holds true. 

This completes the proof of correctness of the majority vote algorithm due to Boyer and Moore.
=======================================================================================
====
### Instruction:<｜begin▁of▁sentence｜>
# Comments:
The set of valid indices in a one-indexed sequence s
The length of one-indexed sequence s
Converts from a zero-indexed sequence to a one-indexed sequence
Converts from a one-indexed sequence to a zero-indexed sequence
Lexicographic order on one-indexed sequences a and b
Rotate the string s to the left by r indices
The set of all rotations of one-indexed sequence s
**************************************************************************)
Defines operators on finite one-indexed sequences, where a sequence of  *)
length n is represented as a function whose domain is the set 1..(n+1)   *)
(the set {1, 2, ... , n}).                                               *)
**************************************************************************)
### Response:
(*************************************************************************)
(* Defines operators on finite one-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 1..(n+1) *)
(* (the set {1, 2, ... , n}).                                               *)
(*************************************************************************)

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
  
\* The set of valid indices in a one-indexed sequence s
OIndices(s) ==
  IF s = EmptySequence
  THEN {}
  ELSE DOMAIN (s EXCEPT {0}) + 1

\* The length of one-indexed sequence s
OLen(s) ==
  IF s = EmptySequence
  THEN 0
  ELSE MAXIMUM OIndices(s)

\* Converts from a zero-indexed sequence to a one-indexed sequence
OSeqFromSeq(seq) ==
  [i \in ZIndices(seq) |-> seq[i]] EXCEPT {0} + 1

\* Converts from a one-indexed sequence to a zero-indexed sequence
SeqFromOSeq(oseq) ==
  [i \in OIndices(oseq) - 1 |-> oseq[i]]

\* Lexicographic order on one-indexed sequences a and b
a \preceq b ==
  LET
    s1len == OLen(a)
    s2len == OLen(b)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len /\ i = s2len -> TRUE
       [] s1[i] < s2[i] -> TRUE
       [] s1[i] > s2[i] -> FALSE
       [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(a, b, 1)

\* Rotate the string s to the left by r indices
ORotation(s, r) ==
  [i \in OIndices(s) |-> s[(i - 1 + r) % (OLen(s)) + 1]]

\* The set of all rotations of one-indexed sequence s
ORotations(s) ==
  {[shift |-> r, seq |-> ORotation(s, r)] : r \in OIndices(s)}

=============================================================================
====