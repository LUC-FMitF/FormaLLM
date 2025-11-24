---- MODULE BinarySearch ----
BEGIN TRANSLATION

CONSTANTS
    Values,
    SortedSeqs,
    Val,
    Seq,
    Len,
    SortedSequence,
    SortedSequences,
    SeqOfLength,
    ZeroZSeq,
    OneZSeq,
    ZLen,
    Rotation,
    Rotations,
    Natural,
    ZeroIndexedSequences,
    ZeroIndexedSequence,
    ZeroIndexedSequencesOfLength,
    SequenceOfLength,
    Sequences,
    Sequence,
    EmptyZSeq,
    SeqFromZSeq,
    ZSeqFromSeq.

LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences.

EmptyZSeq == <>>

ZIndices(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE DOMAIN s

ZSeqOfLength(S, n) ==
  IF n = 0
  THEN {EmptyZSeq}
  ELSE {[i ∈ 0..(n − 1) | → S[i+1]] : i ∈ 0..(n − 1)}

ZSeq(S) == UNION {ZSeqOfLength(S, n) : n ∈ Nat}

ZLen(s) ==
  IF s = EmptyZSeq
  THEN 0
  ELSE Cardinality(DOMAIN s)

ZSeqFromSeq(seq) ==
  IF seq = EmptyZSeq
  THEN EmptyZSeq
  ELSE {[i ∈ 0..(Len(seq) − 1) | → seq[i+1]] : i ∈ 0..(Len(seq) − 1)}

SeqFromZSeq(zseq) ==
  IF zseq = EmptyZSeq
  THEN <>>
  ELSE {[i ∈ 1..ZLen(zseq) | → zseq[i-1]] : i ∈ 1..ZLen(zseq)}

a ≤ b ==
  LET
    s1len == ZLen(a)
    s2len == ZLen(b)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len /\ i = s2len -> s1len <= s2len
      | [] s1[i] < s2[i] -> TRUE
      | [] s1[i] > s2[i] -> FALSE
      | [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(a, b, 0)

Rotation(s, r) ==
  IF s = EmptyZSeq
  THEN EmptyZSeq
  ELSE {[i ∈ ZIndices(s) | -> s[(i + r) % ZLen(s)]]}

Rotations(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE {[
      shift | -> r,
      seq | -> Rotation(s, r)
     ] : r ∈ ZIndices(s)}

PARTIAL CORRECTNESS

The invariant formula resultCorrect is true.

The inductive invariant Inv is defined here.

You can use TLC to check that Inv is an inductive invariant.

PROOFS

Here is the invariance proof.

END TRANSLATION
====