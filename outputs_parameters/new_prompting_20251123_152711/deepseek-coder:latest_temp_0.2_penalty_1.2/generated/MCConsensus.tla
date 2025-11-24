---- MODULE MCConsensus ----
MODULE ZeroIndexedSequences

CONSTANTS Value = {"a", "b", "c"}

SPECIFICATION ISpec
INVARIANT Inv

CHECK_DEADLOCK FALSE

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

EmptyZSeq == <<>>

ZIndices(s) ==
  IF s == EmptyZSeq
  THEN {}
  ELSE DOMAIN s

ZSeqOfLength(S, n) ==
  IF n == 0
  THEN {EmptyZSeq}
  ELSE [0..(n-1) -> S]

ZSeq(S) == UNION {ZSeqOfLength(S, n) : n IN Nat}

ZLen(s) ==
  IF s == EmptyZSeq
  THEN 0
  ELSE Cardinality(DOMAIN s)

ZSeqFromSeq(seq) ==
  IF seq == <<>>
  THEN EmptyZSeq
  ELSE [i IN 0..(Len(seq)-1) |-> seq[i+1]]

SeqFromZSeq(zseq) ==
  IF zseq == EmptyZSeq
  THEN <<>>
  ELSE [i IN 1..ZLen(zseq) |-> zseq[i-1]]

a preceq b ==
  LET
    s1len == ZLen(a)
    s2len == ZLen(b)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i == s1len /\ i == s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(a, b, 0)

Rotation(s, r) ==
  IF s == EmptyZSeq
  THEN EmptyZSeq
  ELSE [i IN ZIndices(s) |-> s[(i + r) % ZLen(s)]]

Rotations(s) ==
  IF s == EmptyZSeq
  THEN {}
  ELSE [
      shift |-> r,
      seq   |-> Rotation(s, r)
     ] : r IN ZIndices(s)

Inv' ==
  [Next]_chosen

Inv ==
  [Inv' : Next]_chosen

which is equivalent to checking

Inv ==
  [Inv' : [][Next]_chosen]

which asserts that Inv is an invariant of the spec

Inv ==
  [Inv' : [][Next]_chosen]

END MODULE
====