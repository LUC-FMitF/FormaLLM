---- MODULE ClientCentric ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS InitValue = _|_ (* TODO: InitValue could be bottom (_|_) *)

(* Types and Invariants *)
TypeOK [EmptyZSeq] 1
TypeOK [ZIndices(s)] SetOf[NaturalNumber]
TypeOK [ZSeqOfLength(S, n)] Sequence[0 .. (n - 1), ElementOf[S]]
TypeOK [ZSeq(S)] Union[{ZSeqOfLength(S, n) : n \in Nat}]
TypeOK [ZLen(s)] NaturalNumber
TypeOK [ZSeqFromSeq(seq)] Sequence[0 .. (Len(seq)-1), ElementOf[Domain(seq)]]
TypeOK [SeqFromZSeq(zseq)] SetOf[Tuple{ElementOf[NaturalNumber], ElementOf[zseq[ZIndices(zseq)]]}]
TypeOK [a \preceq b] Boolean
TypeOK [Rotation(s, r)] Sequence[(0 .. (ZLen(s) - 1))-set((r % ZLen(s))) \subseteq Domain(s), ElementOf[Domain(s)]]
TypeOK [Rotations(s)] SetOf[Tuple{ElementOf[NaturalNumber], Sequence[0 .. (ZLen(s)-1), ElementOf[Domain(s)]]}]

(* Comments: *)
\* The empty zero-indexed sequence *
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s *
ZIndices(s) == IF s = EmptyZSeq THEN {} ELSE Domain(s)

\* The set of all zero-indexed sequences of elements in S with length n *
ZSeqOfLength(S, n) == IF n = 0 THEN {EmptyZSeq} ELSE [i \in 0 .. (n - 1) |-> S]

\* The set of all zero-indexed sequences of elements in S *
ZSeq(S) == Union{ZSeqOfLength(S, n): n \in Nat}

\* The length of zero-indexed sequence s *
ZLen(s) == IF s = EmptyZSeq THEN 0 ELSE Cardinality(Domain(s))

\* Converts from a one-indexed sequence to a zero-indexed sequence *
ZSeqFromSeq(seq) == IF seq = <<>> THEN EmptyZSeq ELSE [i \in 0 .. (Len(seq)-1) |-> seq[i+1]]

\* Converts from a zero-indexed sequence to a one-indexed sequence *
SeqFromZSeq(zseq) == IF zseq = EmptyZSeq THEN <<>> ELSE [i \in 1 .. ZLen(zseq) |-> zseq[i-1]]

\* Lexicographic order on zero-indexed sequences a and b *
a \preceq b == LET s1len = ZLen(a), s2len = ZLen(b), IsLexLeq(_, _, _) == CASE i = s1len /\ i = s2len -> s1len <= s2len [] s1[i] < s2[i] -> TRUE [] s1[i] > s2[i] -> FALSE [ OTHER -> IsLexLeq(s1, s2, i + 1) ] IN IsLexLeq(a, b, 0)

\* Rotate the string s to the left by r indices *
Rotation(s, r) == IF s = EmptyZSeq THEN EmptyZSeq ELSE [i \in ZIndices(s) |-> s[(i + r) % ZLen(s)]]

\* The set of all rotations of zero-indexed sequence s *
Rotations(s) == IF s = EmptyZSeq THEN {} ELSE {[shift |-> r, seq |-> Rotation(s, r)] : r \in ZIndices(s)}

(* TLC Configuration: *)
CONSTANTS InitValue = 0 (* Initial value for keys in state. *)

SPECIFICATION Spec == [...] (* TODO: Your isolation level specification goes here. *)

INVARIANTS Inv == [...] (* TODO: Your invariants go here. *)
====