---- MODULE ZSequences 
------------------------------ MODULE ZSequences 
(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of  *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, 2, 3}).                                                 *)
(***************************************************************************)

CONSTANTS Value = {"a", "b", "c"}

\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE DOMAIN s

\* The set of all zero-indexed sequences of elements in S with length n
LOCAL ZSeqOfLength(S, n) ==
  IF n = 0
  THEN {EmptyZSeq}
  ELSE [0 .. (n - 1) -> S]

\* The set of all zero-indexed sequences of elements in S
ZSeq(S) == UNION {ZSeqOfLength(S, n) : n \in Nat}

\* The length of zero-indexed sequence s
ZLen(s) ==
  IF s = EmptyZSeq
  THEN 0
  ELSE Cardinality(DOMAIN s)

\* Converts from a one-indexed sequence to a zero-indexed sequence
ZSeqFromSeq(seq) ==
  IF seq = <<>>
  THEN EmptyZSeq
  ELSE [i \in 0..(Len(seq)-1) |-> seq[i+1]]

\* Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) ==
  IF zseq = EmptyZSeq
  THEN <<>>
  ELSE [i \in 1..ZLen(zseq) |-> zseq[i-1]]

\* Lexicographic order on zero-indexed sequences a and b
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

\* Rotate the string s to the left by r indices
Rotation(s, r) ==
  IF s = EmptyZSeq
  THEN EmptyZSeq
  ELSE [i \in ZIndices(s) |-> s[(i + r) % ZLen(s)]]

\* The set of all rotations of zero-indexed sequence s
Rotations(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE {[
      shift |-> r,
      seq   |-> Rotation(s, r)
    ] : r \in ZIndices(s)
  }

=============================================================================
====

\* ISpec is the specification
ISpec == []Inv /\ [][Next]_chosen

\* Inv is the invariant
Inv == []Inv /\ [][Next]_chosen

\* TLC Configuration
TLC_CONFIG
CONSTANTS Value = {"a", "b", "c"}
SPECIFICATION ISpec
INVARIANT Inv
CHECK_DEADLOCK FALSE
=============================================================================
====

Note: The above TLA+ code is a basic example of how to define and use zero-indexed sequences. It does not include all possible operations or edge cases, and should be adapted to fit the specific needs of your project.
====