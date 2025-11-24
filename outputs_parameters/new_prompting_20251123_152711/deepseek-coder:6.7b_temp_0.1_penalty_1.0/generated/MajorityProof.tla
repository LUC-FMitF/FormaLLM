---- MODULE MajorityProof ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of  *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ... , n-1}).                                             *)
(***************************************************************************)

CONSTANTS
  EmptySet == {}

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
  
\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) ==
  IF s = EmptyZSeq
  THEN EmptySet
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
  IF seq = EmptyZSeq
  THEN EmptyZSeq
  ELSE [i \in 0..(Len(seq)-1) |-> seq[i+1]]

\* Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) ==
  IF zseq = EmptyZSeq
  THEN EmptyZSeq
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
  ELSE [i \in ZIndices(s) |-> s[(i + r) MOD ZLen(s)]]

\* The set of all rotations of zero-indexed sequence s
Rotations(s) ==
  IF s = EmptyZSeq
  THEN EmptySet
  ELSE {[
      shift |-> r,
      seq   |-> Rotation(s, r)
    ] : r \in ZIndices(s)
  }

=============================================================================
====

(* TLC Configuration *)
CONSTANTS
  S == {0, 1}
  n == 5

SPECIFICATION
  ZSeq(S) = {EmptyZSeq, <<0, 1, 0, 1, 0>>, <<0, 0, 1, 1, 0>>, <<1, 0, 0, 1, 0>>, <<1, 1, 0, 0, 1>>, <<0, 1, 1, 0, 0>>}
  ZLen(EmptyZSeq) = 0
  ZLen(<<0, 1, 0, 1, 0>>) = 5
  ZSeqFromSeq(<<>>) = EmptyZSeq
  ZSeqFromSeq(<<0, 1, 0, 1, 0>>) = <<0, 1, 0, 1, 0>>
  SeqFromZSeq(EmptyZSeq) = <<>>
  SeqFromZSeq(<<0, 1, 0, 1, 0>>) = <<0, 1, 0, 1, 0>>
  a \preceq b ==> a \preceq b
  Rotation(EmptyZSeq, r) = EmptyZSeq
  Rotation(<<0, 1, 0, 1, 0>>, r) = <<0, 1, 0, 1, 0>>
  Rotations(EmptyZSeq) = EmptySet
  Rotations(<<0, 1, 0, 1, 0>>) = {[shift |-> 0, seq |-> <<0, 1, 0, 1, 0>>], [shift |-> 1, seq |-> <<1, 0, 0, 1, 0>>], [shift |-> 2, seq |-> <<0, 0, 1, 1, 0>>], [shift |-> 3, seq |-> <<0, 1, 0, 1, 0>>], [shift |-> 4, seq |-> <<0, 1, 0, 1, 0>>]}

INVARIANTS
  TypeOK
  ZSeq(S) \in Sequences
  ZLen(s) \in Nat
  ZSeqFromSeq(seq) \in ZSeq(Seq(S))
  SeqFromZSeq(zseq) \in Seq(ZSeq(S))
  a \preceq b ==> a \preceq b
  Rotation(s, r) \in ZSeq(S)
  Rotations(s) \in Powerset(ZSeq(S))

(* Proofs *)
THEOREM
  [[](ZSeq(S) \in Sequences) /\
   [](\E s \in ZSeq(S) : ZLen(s) \in Nat) /\
   [](\E s \in ZSeq(S) : \E seq : Seq(S) : s = ZSeqFromSeq(seq)) /\
   [](\E seq : Seq(S) : seq = SeqFromZSeq(ZSeqFromSeq(seq))) /\
   [](\E a, b : ZSeq(S) : a \preceq b ==> a \preceq b) /\
   [](\E s : ZSeq(S) : \E r : Nat : Rotation(s, r) \in ZSeq(S)) /\
   [](\E s : ZSeq(S) : Rotations(s) \in Powerset(ZSeq(S)))
  ] ==> []TypeOK
====