---- MODULE MajorityProof ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of  *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ... , n-1}).                                             *)
(***************************************************************************)

CONSTANTS Naturals == [0 .. Infinity - 1]
INSTANCE FiniteSets
INSTANCE Sequences

\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) == IF s = EmptyZSeq THEN {} ELSE DOMAIN s

\* The set of all zero-indexed sequences of elements in S with length n
LOCAL ZSeqOfLength(S, n) == IF n = 0 THEN {EmptyZSeq} ELSE [0 .. (n - 1)] := S

\* The set of all zero-indexed sequences of elements in S
ZSeq(S) == UNION {ZSeqOfLength(S, n): n \in Naturals}

\* The length of zero-indexed sequence s
ZLen(s) == IF s = EmptyZSeq THEN 0 ELSE Cardinality(DOMAIN s)

\* Converts from a one-indexed sequence to a zero-indexed sequence
ZSeqFromSeq(seq) == IF seq = EmptyZSeq THEN EmptyZSeq ELSE [i \in 0..Cardinality(seq)-1] := seq[i+1]

\* Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) == IF zseq = EmptyZSeq THEN EmptyZSeq ELSE [i \in 1..Cardinality(zseq)] := zseq[i]

\* Lexicographic order on zero-indexed sequences a and b
a <= b == LET s1len,s2len == ZLen(a),ZLen(b) IS (s1len = s2len /\ <<>> <= [0..s1len - 1] := a[i] < b[i])

\* Rotate the string s to the left by r indices
Rotation(s, r) == IF s = EmptyZSeq THEN EmptyZSeq ELSE [i \in ZIndices(s)] := s[(i + r) MOD Cardinality(s)]

\* The set of all rotations of zero-indexed sequence s
Rotations(s) == IF s = EmptyZSeq THEN {} ELSE {[i \in 0..Cardinality(s)-1] := Rotation(s, i)}

=============================================================================

(* The empty zero-indexed sequence *)
EmptyZSeq == <<>>

\* TypeOK for type invariants
TYPEOK INVARIANTS

\* Define all symbols before use *)
CONSTANTS Naturals, FiniteSets, Sequences
INSTANCE ZSequences

\* Include TLC config after 
(* Proving type correctness is easy. *)
(* Auxiliary lemmas about positions and occurrences. *)
(* We prove correctness based on the inductive invariant. *)
TLC \*\*/\*.tla
====