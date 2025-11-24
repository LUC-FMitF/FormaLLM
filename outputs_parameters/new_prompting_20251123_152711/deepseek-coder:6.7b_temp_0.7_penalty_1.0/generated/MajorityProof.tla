---- MODULE MajorityProof ------------------------------------------------------------

-- Module for handling zero-indexed sequences

CONSTANTS
  EmptyZSeq == <<>>

VARIABLES
  ZIndices, ZSeqOfLength, ZSeq, ZLen, ZSeqFromSeq, SeqFromZSeq, Rotation, Rotations

-- The set of valid indices for zero-indexed sequence s
ZIndices(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE DOMAIN s

-- The set of all zero-indexed sequences of elements in S with length n
ZSeqOfLength(S, n) ==
  IF n = 0
  THEN {EmptyZSeq}
  ELSE [0 .. (n - 1) -> S]

-- The set of all zero-indexed sequences of elements in S
ZSeq(S) == UNION {ZSeqOfLength(S, n) : n \in Nat}

-- The length of zero-indexed sequence s
ZLen(s) ==
  IF s = EmptyZSeq
  THEN 0
  ELSE Cardinality(DOMAIN s)

-- Converts from a one-indexed sequence to a zero-indexed sequence
ZSeqFromSeq(seq) ==
  IF seq = EmptyZSeq
  THEN EmptyZSeq
  ELSE [i \in 0..(Len(seq)-1) |-> seq[i+1]]

-- Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) ==
  IF zseq = EmptyZSeq
  THEN EmptyZSeq
  ELSE [i \in 1..ZLen(zseq) |-> zseq[i-1]]

-- Lexicographic order on zero-indexed sequences a and b
a \preceq b ==
  LET
    s1len == ZLen(a)
    s2len == ZLen(b)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len /\ i = s2len -> s1len <= s2len
       [] s1[i] < s2[i] -> TRUE
       [] s1[i] > s2[i] -> FALSE
       [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(a, b, 0)

-- Rotate the string s to the left by r indices
Rotation(s, r) ==
  IF s = EmptyZSeq
  THEN EmptyZSeq
  ELSE [i \in ZIndices(s) |-> s[(i + r) MOD ZLen(s)]]

-- The set of all rotations of zero-indexed sequence s
Rotations(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE { [shift \in 0..ZLen(s)-1 |-> Rotation(s, shift) ] }

=============================================================================
====

TLC Configuration:

CONSTANTS
  PositiveInt == {1 .. Infinity}

SPECIFICATION ZSequences

INVARIANTS
  TypeOK,
  ZSeqTypeOK == ZLen(s) \in Nat /\ ZIndices(s) \subseteq Nat /\ ZSeqOfLength(S, n) \subseteq ZSeq(S) /\
                ZLen(ZSeqFromSeq(SeqFromZSeq(s))) = ZLen(s) /\ SeqFromZSeq(ZSeqFromSeq(s)) = s /\
                ZSeq(S) \cap {s : s \in ZSeq /\ ZLen(s) > 0} = {} /\
                ZLen(Rotation(s, r)) = ZLen(s) /\ Rotation(s, r) \in ZSeq(ZIndices(s)) /\
                Rotations(s) \subseteq ZSeq(ZIndices(s))
====