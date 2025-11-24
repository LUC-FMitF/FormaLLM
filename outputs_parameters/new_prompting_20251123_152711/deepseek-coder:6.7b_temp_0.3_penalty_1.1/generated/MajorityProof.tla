---- MODULE MajorityProof ----
(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of  *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ... , n-1}).                                             *)
(***************************************************************************)

CONSTANTS
EmptyZSeq == <<>>
Nat == {0, 1, 2, ...}
FiniteSets == POWERSET Nat
Sequences == FUNCTION FiniteSets -> PowersetOfNat

(* The empty zero-indexed sequence *)
EmptyZSeq == 
    [n \in Nat |-> EmptySet]

(* The set of valid indices for zero-indexed sequence s *)
ZIndices(s) == DOMAIN s

(* The set of all zero-indexed sequences of elements in S with length n *)
ZSeqOfLength(S, n) == 
    [i \in 0..n-1 |-> S]

(* The set of all zero-indexed sequences of elements in S *)
ZSeq(S) == UNION {ZSeqOfLength(S, n) : n \in Nat}

(* The length of zero-indexed sequence s *)
ZLen(s) == 
    IFEXIST i \in ZIndices(s) THEN Cardinality(DOMAIN s) ELSE 0

(* Converts from a one-indexed sequence to a zero-indexed sequence *)
ZSeqFromSeq(seq) ==
    [i \in Nat |-> IFEXIST j=i+1 THEN seq[j] ELSE EmptySet]

(* Converts from a zero-indexed sequence to a one-indexed sequence *)
SeqFromZSeq(zseq) == 
    [i \in 1..ZLen(zseq) |-> zseq[i-1]]

(* Lexicographic order on zero-indexed sequences a and b *)
a <= b ==
    LET len = ZLen(a),
        IsLexLeq(_, _, _) IS [len, a, b] /\ 
            (len = 0 \/ EXIST i IN 0..len-1 /\ a[i]=b[i])
        VARIANTS
            len = 0 -> TRUE
            len > 0 /\ a[0] < b[0] -> TRUE
            len > 0 /\ a[0] > b[0] -> FALSE
            OTHERWISE IsLexLeq(len-1, [i \in 1..len-1 |-> a[i+1]], [i \in 1..len-1 |-> b[i+1]])
    IN IsLexLeq(len, a, b)

(* Rotate the string s to the left by r indices *)
Rotation(s, r) == 
    [i \in ZIndices(s) |-> s[(i + r) MOD ZLen(s)]]

(* The set of all rotations of zero-indexed sequence s *)
Rotations(s) == {[shift |-> r, seq |-> Rotation(s, r)] : r \in ZIndices(s)}

=============================================================================
CONSTANTS
EmptySet == {}
PowersetOfNat == POWERSET Nat

(* Auxiliary lemmas about positions and occurrences *)
LemmaPositions == 
    [i \in 0..ZLen(s)-1 |-> (EXIST j IN ZIndices(s) /\ s[j]=a[i])]
LemmaOccurrences == 
    [a[i] |-> 1 + Sum{b \in a[0..i-1] : LemmaPositions[b]} ]

(* Proving type correctness is easy *)
TypeOK == EXIST s IN Sequences /\ ZLen(s) = Cardinality(DOMAIN s)

(* We prove correctness based on the inductive invariant *)
InductiveInvariant == 
    [n \in Nat |-> (EXIST s IN ZSeqOfLength(PowersetOfNat, n) 
                     /\ ZLen(s) = Cardinality(DOMAIN s))]

====
(* TLC Configuration *)
CONSTANTS
EmptySequence == <<>>
NonNegativeIntegers == {0, 1, 2, ...}
FiniteSets == POWERSET NonNegativeIntegers
Sequences == FUNCTION FiniteSets -> PowersetOfNat

(* Auxiliary lemmas about positions and occurrences *)
LemmaPositions == 
    [i \in 0..Len(s)-1 |-> (EXIST j IN Domain(s) /\ s[j]=a[i])]
LemmaOccurrences == 
    [a[i] |-> 1 + Sum{b \in a[0..i-1] : LemmaPositions[b]} ]

(* Proving type correctness is easy *)
TypeOK == EXIST s IN Sequences /\ Len(s) = Cardinality(Domain(s))

(* We prove correctness based on the inductive invariant *)
InductiveInvariant == 
    [n \in NonNegativeIntegers |-> (EXIST s IN ZSeqOfLength(PowersetOfNat, n) 
                                     /\ Len(s) = Cardinality(Domain(s)))]

====
***************************************************************************)
Proving type correctness is easy.                                        *)
***************************************************************************)
Auxiliary lemmas about positions and occurrences.                        *)
***************************************************************************)
We prove correctness based on the inductive invariant.                   *)
***************************************************************************)
### Instruction:<｜begin▁of▁sentence｜>
Generate complete TLA+ module with TLC config. Follow all previous rules and syntax.

# Comments:
**************************************************************************)
Proving type correctness is easy.                                        *)
**************************************************************************)
Auxiliary lemmas about positions and occurrences.                        *)
**************************************************************************)
We prove correctness based on the inductive invariant.                   *)
***************************************************************************)
(* TLC Configuration *)
CONSTANTS
EmptySequence == <<>>
NonNegativeIntegers == {0, 1, 2, ...}
FiniteSets == POWERSET NonNegativeIntegers
Sequences == FUNCTION FiniteSets -> PowersetOfNat

(* Auxiliary lemmas about positions and occurrences *)
LemmaPositions == 
    [i \in 0..Len(s)-1 |-> (EXIST j IN Domain(s) /\ s[j]=a[i])]
LemmaOccurrences == 
    [a[i] |-> 1 + Sum{b \in a[0..i-1] : LemmaPositions[b]} ]

(* Proving type correctness is easy *)
TypeOK == EXIST s IN Sequences /\ Len(s) = Cardinality(Domain(s))

(* We prove correctness based on the inductive invariant *)
InductiveInvariant == 
    [n \in NonNegativeIntegers |-> (EXIST s IN ZSeqOfLength(PowersetOfNat, n) 
                                     /\ Len(s) = Cardinality(Domain(s)))]

(* Specification *)
Spec == []TypeOK /\ InductiveInvariant

====
*)
====