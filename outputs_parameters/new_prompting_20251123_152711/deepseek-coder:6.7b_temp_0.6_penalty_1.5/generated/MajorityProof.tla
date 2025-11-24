---- MODULE ZSequences  ----
(****************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of   *)
(* length n is represented as a function whose domain is the set 0..(n-1)    *)
(* (the set {0, 1, ... , n-1}).                                             *)
(****************************************************************************)

CONSTANTS EmptyZSeq == <<>>   \* The empty zero-indexed sequence

VARIABLES Sequences, FiniteSets, Naturals

EmptyZSeqOK ~~ [i |-> O]       \* Type OK for the empty zero-indexed sequence
FiniteSetsOK ~~ FINITESET[0 .. n - 1]   \* Type OK for finite sets
NaturalsOK ~~ NATURALNUMBERS                \* Type OK for natural numbers
SequencesOK == [i |-> SUBSET Values & i \in Domain(s)] /\ Cardinality(Domain(s)) = n   \* Type OK for sequences
                                                                                  
ZIndices(s) ~~ {i : s[i] \in Elements}              \* The set of valid indices for zero-indexed sequence s
ZSeqOfLength(S, n) ~~ [i |-> S & i \in Domain(s)]   \* The set of all zero-indexed sequences of elements in S with length n
ZLen(s) == IF s = EmptyZSeq THEN 0 ELSE Cardinality(Domain(s))    \* The length of zero-indexed sequence s
Rotation(s, r) ~~ [i |-> s[(i + r) MOD ZLen(s)]]       \* Rotate the string s to the left by r indices
ZSeqFromSeq(seq) == IF seq = EmptyZSeq THEN EmptyZSeq ELSE [i |-> seq[i + 1]]   \* Converts from a one-indexed sequence to a zero-indexed sequence
SeqFromZSeq(zseq) ~~ IF zseq = EmptyZSeq THEN <<>> ELSE [i |-> zseq[i - 1]]     \* Converts from a zero-indexed sequence to a one-indexed sequence
AuxiliaryPredicate IsLexLeq(_, _, _) == CASE i = ZLen(a) /\ i = ZLen(b) THEN ZLen(a) <= ZLen(b) 
                                             [] a[i] < b[i] THEN TRUE
                                             [] OTHERWISE FALSE
                                             ENDCASE   \* Auxiliary lemmas about positions and occurrences
Rotations(s) ~~ {r |-> r, seq |-> [i |-> s[(i + r) MOD ZLen(s)]]}      \* The set of all rotations of zero-indexed sequence s

Spec == [] (EmptyZSequencesOK /\ SequencesOK /\ FiniteSetsOK /\ NaturalsOK 
            /\ ZIndicesOK /\ ZSeqOfLengthOK /\ ZLenOK /\ RotationOK 
            /\ ZSeqFromSeqOK /\ SeqFromZSeqOK /\ IsLexLeqOK)   \* The specification

Inv == [s |-> TRUE]                                                       \* The inductive invariant

NextState == ~ (a[i] = b[j]) => a[i + 1 .. n - 1] = b[j + 1 .. n - 1]      \* The next state relation

TLC Configuration:
CONSTANTS Values == {0, 1}   \* Define all symbols before use
SPECIFICATION Spec
INVARIANTS Inv
=============================================================================
====
****************************************************************************)
We prove correctness based on the inductive invariant.                   *)
****************************************************************************)
Lemma1: [] (a[i] = b[j]) => i <= j /\ a[i + 1 .. n - 1] = b[j + 1 .. n - 1]   \* Lemma about positions and occurrences
Proof: By the definition of `IsLexLeq`, we have that if `a[i] = b[j]` then either `ZLen(a) <= ZLen(b)` or `a[i + 1 .. n - 1] = b[j + 1 .. n - 1]`.
QED.

Lemma2: [] (n > 0 /\ i < n - 1) => a[i + 1] \in Values   \* Lemma about the values in sequences
Proof: By definition of `SequencesOK`, we have that `a[i + 1] = s[(i + 1)]` for some `s`. Since `s` is a sequence and `0 <= i < n - 1`, we know that `s[(i + 1)] \in Values`.
QED.

Theorem: [] (n > 0 /\ a[0] = 0) => a[i] \in Values   \* Theorem about the values in sequences
Proof: By induction on `i`, we have that if `a[i - 1] = s[(i - 1)]` for some sequence `s` then `a[i] = (s[(i - 1)] + 1) MOD n`. Since `0 <= i < n` and `n > 0`, we know that `(s[(i - 1)] + 1) MOD n \in Values`.
QED.

Theorem: [] Inv => (Rotation(a, r))[i] = a[(i + r) MOD ZLen(a)]   \* Theorem about the rotation of sequences
Proof: By induction on `i`, we have that if `Inv[s]` then for all `r`, `Rotation(a, r)[i] = a[(i + r) MOD ZLen(a)]`. Since `0 <= i < n` and `n > 0`, we know that `((s[(i - 1)] + 1) MOD n) \in Values`.
QED.

Corollary: [] Inv => a = b   \* Corollary about the equality of sequences
Proof: By Lemma1 and Theorem2, if `Inv[a]` then for all `r`, `Rotation(a, r) = a`. Since `0 <= i < n` and `n > 0`, we know that `((s[(i - 1)] + 1) MOD n) \in Values`.
QED.
=============================================================================
TLC Configuration:
CONSTANTS Values == {0, 1}   \* Define all symbols before use
SPECIFICATION Spec
INVARIANTS Inv
=============================================================================
====
****************************************************************************)
Proving type correctness is easy.                                        *)
****************************************************************************)
Lemma: [] SequencesOK => [i |-> s[i] \in Values & i \in Domain(s)] /\ Cardinality(Domain(s)) = n   \* Lemma about the values in sequences
Proof: By definition of `SequencesOK`, we have that for all `i` such that `0 <= i < n`, `s[i] \in Values & i \in Domain(s)` and `Cardinality(Domain(s)) = n`.
QED.

Theorem: [] Spec => [i |-> s[i] \in Values & i \in Domain(s)] /\ Cardinality(Domain(s)) = n   \* Theorem about the values in sequences
Proof: By induction on `n`, we have that if `Spec` then for all `s` such that `SequencesOK[s]`, `[i |-> s[i] \in Values & i \in Domain(s)] /\ Cardinality(Domain(s)) = n`.
QED.
=============================================================================
TLC Configuration:
CONSTANTS Values == {0, 1}   \* Define all symbols before use
SPECIFICATION Spec
INVARIANTS Inv
=============================================================================
====
****************************************************************************)
*)
isabelle_system "exit" (* Exit the Isabelle system *)
end

end
====