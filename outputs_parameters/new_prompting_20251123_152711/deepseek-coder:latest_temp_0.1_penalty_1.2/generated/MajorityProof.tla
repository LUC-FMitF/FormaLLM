---- MODULE MajorityProof --------

(***************************************************************************)
(* We prove correctness based on the inductive invariant.                   *)
(***************************************************************************)

INITIAL INSTANCE Sequences
LOCAL INSTANCE Naturals
LOCAL INSTANCE Positions
LOCAL INSTANCE Occurrences

\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE DOMAIN s

\* The set of all zero-indexed sequences of elements in S with length n
LOCAL ZSeqOfLength(S, n) ==
  IF n = Zero
  THEN  {EmptyZSeq}
  ELSE {i ∈ Naturals : i → S[i]}

\* The set of all zero-indexed sequences of elements in S
ZSeq(S) == UNION {ZSeqOfLength(S, n) : n ∈ Naturals}

\* The length of zero-indexed sequence s
ZLen(s) ==
  IF s = EmptyZSeq
  THEN Zero
  ELSE CARD(DOMAIN s)

\* Converts from a one-indexed sequence to a zero-indexed sequence
ZSeqFromSeq(seq) ==
  IF seq = <<>>
  THEN EmptyZSeq
  ELSE {i ∈ ZIndices(seq) : i → seq[i+1]}

\* Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) ==
  IF zseq = EmptyZSeq
  THEN <<>>
  ELSE {i ∈ Naturals : i → zseq[i-1]}

\* Lexicographic order on zero-indexed sequences a and b
a ≤ b ∈ {s1 ∈ ZSeq(a) : s2 ∈ ZSeq(b) : s1 ≤ s2}

\* Rotate the string s to the left by r indices
Rotation(s, r) ∈ {i ∈ ZIndices(s) : i → s[(i + r) ⌊ ZLen(s) ≥ r]}

\* The set of all rotations of zero-indexed sequence s
Rotations(s) ∈ {i ∈ ZIndices(s) : i → Rotation(s, i)}

=============================================================================
====