---- MODULE SimpleRegular ----
EXTENDS FiniteSets, Naturals, Sequences
CONSTANTS N = 8
VARIABLES
  EmptyZSeq == <<>>
  ZIndices(s) ==
    IF s = EmptyZSeq
    THEN {}
    ELSE DOMAIN s
  ZSeqOfLength(S, n) ==
    IF n = 0
    THEN {EmptyZSeq}
    ELSE [0 .. (n - 1) -> S]
  ZSeq(S) == UNION {ZSeqOfLength(S, n) : n \in Nat}
  ZLen(s) ==
    IF s = EmptyZSeq
    THEN 0
    ELSE Cardinality(DOMAIN s)
  ZSeqFromSeq(seq) ==
    IF seq = <<>>
    THEN EmptyZSeq
    ELSE [i \in 0..(Len(seq)-1) |-> seq[i+1]]
  SeqFromZSeq(zseq) ==
    IF zseq = EmptyZSeq
    THEN <<>>
    ELSE [i \in 1..ZLen(zseq) |-> zseq[i-1]]
  ZSeqLexLeq(a, b) ==
    LET
      s1len == ZLen(a)
      s2len == ZLen(b)
      RECURSIVE IsLexLeq(_, _, _)
      IsLexLeq(s1, s2, i) ==
        CASE i = s1len \/ i = s2len -> s1len <= s2len
        [] s1[i] < s2[i] -> TRUE
        [] s1[i] > s2[i] -> FALSE
        [] OTHER -> IsLexLeq(s1, s2, i + 1)
    IN IsLexLeq(a, b, 0)
  Rotation(s, r) ==
    IF s = EmptyZSeq
    THEN EmptyZSeq
    ELSE [i \in ZIndices(s) |-> s[(i + r) % ZLen(s)]]
  ZSeqRotations(s) ==
    IF s = EmptyZSeq
    THEN {}
    ELSE {[
        shift |-> r,
        seq   |-> Rotation(s, r)
      ] : r \in ZIndices(s)
    }
INIT
  Init ==
    ![i \in 0..(N-1) |-> x[i] = {0} /\ y[i] = 0]
NEXT
  Next ==
    ![i \in 0..(N-1) |->
      IF i = 0
      THEN
        x[i] = {0,1} /\ y[i] = 0
      ELSE
        x[i] = {1} /\ y[i] = x[(i-1) % N]
    ]
SPEC
  Spec ==
    Init /\
    [][Next]_<<x, y>>
INVARIANTS
  PCorrect ==
    ![i \in 0..(N-1) |->
      IF i = 0
      THEN
        x[i] = {0,1} /\ y[i] = 0
      ELSE
        x[i] = {1} /\ y[i] = x[(i-1) % N]
    ]
  TypeOK ==
    ![i \in 0..(N-1) |->
      IF i = 0
      THEN
        x[i] = {0,1} /\ y[i] = 0
      ELSE
        x[i] = {1} /\ y[i] = x[(i-1) % N]
    ]
  Inv ==
    ![i \in 0..(N-1) |->
      IF i = 0
      THEN
        x[i] = {0,1} /\ y[i] = 0
      ELSE
        x[i] = {1} /\ y[i] = x[(i-1) % N]
    ]
=============================================================================
====