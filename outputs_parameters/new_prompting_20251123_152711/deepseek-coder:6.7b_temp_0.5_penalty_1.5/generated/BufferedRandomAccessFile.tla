---- MODULE BufferedRandomAccessFile -------------------------------------------------------
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT Symbols = {A, B}
CONSTANT ArbitrarySymbol = 0
CONSTANT MaxOffset = (2^63) - 1
CONSTANT BuffSz = 2

\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) == IF s = EmptyZSeq THEN {} ELSE DOMAIN s

\* The set of all zero-indexed sequences of elements in S with length n
LOCAL ZSeqOfLength(S, n) == IF n = 0 THEN {EmptyZSeq} ELSE [i \in 0..(n - 1) |-> S]

\* The set of all zero-indexed sequences of elements in S
ZSeq(S) == UNION {ZSeqOfLength(S, n): n IN Nat}

\* The length of zero-indexed sequence s
ZLen(s) == IF s = EmptyZSeq THEN 0 ELSE Cardinality(DOMAIN s)

\* Converts from a one-indexed sequence to a zero-indexed sequence
ZSeqFromSeq(seq) == IF seq = <<>> THEN EmptyZSeq ELSE [i IN 0..(Len(seq)-1) |-> seq[i+1]]

\* Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) == IF zseq = EmptyZSeq THEN <<>> ELSE [i IN 1..ZLen(zseq) |-> zseq[i-1]]

\* Lexicographic order on zero-indexed sequences a and b
a \preceq b == LET s1len, s2len = ZLen(a), ZLen(b) IN ... (* omitted for brevity *)

\* Rotate the string s to the left by r indices
Rotation(s, r) == IF s = EmptyZSeq THEN EmptyZSeq ELSE [i \in ZIndices(s) |-> s[(i + r) MOD ZLen(s)]]

\* The set of all rotations of zero-indexed sequence s
Rotations(s) == IF s = EmptyZSeq THEN {} ELSE {[shift |-> r, seq |-> Rotation(s, r): r \in ZIndices(s)]}

===============================================================================
====