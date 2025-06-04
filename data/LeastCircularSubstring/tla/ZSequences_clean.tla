------------------------------ MODULE ZSequences ----------------------------

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

EmptyZSeq == <<>>

ZIndices(s) ==
IF s = EmptyZSeq
THEN {}
ELSE DOMAIN s

LOCAL ZSeqOfLength(S, n) ==
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

a \preceq b ==
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

Rotations(s) ==
IF s = EmptyZSeq
THEN {}
ELSE {[
shift |-> r,
seq   |-> Rotation(s, r)
] : r \in ZIndices(s)
}

=============================================================================
