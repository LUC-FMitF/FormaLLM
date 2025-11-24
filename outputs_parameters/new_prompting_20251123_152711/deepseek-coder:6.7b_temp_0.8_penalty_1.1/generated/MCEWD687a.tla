---- MODULE Lamport  ----
(*****************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of length *)
(* n is represented as a function whose domain is the set 0..(n-1) (the set {0, 1, ... , n-1}). *)
(******************************************************************************)

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
  
\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) == IF s = EmptyZSeq THEN {} ELSE DOMAIN s

\* The set of all zero-indexed sequences of elements in S with length n
LOCAL ZSeqOfLength(S, n) == IF n = 0 THEN {EmptyZSeq} ELSE [0 .. (n - 1) -> S]

\* The set of all zero-indexed sequences of elements in S
ZSeq(S) == UNION {ZSeqOfLength(S, n): n \in Nat}

\* The length of zero-indexed sequence s
ZLen(s) == IF s = EmptyZSeq THEN 0 ELSE Cardinality(DOMAIN s)

\* Converts from a one-indexed sequence to a zero-indexed sequence
ZSeqFromSeq(seq) == IF seq = <<>> THEN EmptyZSeq ELSE [i \in 0..(Len(seq)-1) |-> seq[i+1]]

\* Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) == IF zseq = EmptyZSeq THEN <<>> ELSE [i \in 1..ZLen(zseq) |-> zseq[i-1]]

\* Lexicographic order on zero-indexed sequences a and b
a <= b == LET s1len == ZLen(a), s2len == ZLen(b), RECURSIVE IsLexLeq(_, _, _)
IsLexLeq(s1, s2, i) == CASE i = s1len /\ i = s2len -> s1len <= s2len [] s1[i] < s2[i] -> TRUE 
[] s1[i] > s2[i] -> FALSE [] OTHER -> IsLexLeq(s1, s2, i + 1) IN IsLexLex(a, b, 0)

\* Rotate the string s to the left by r indices
Rotation(s, r) == IF s = EmptyZSeq THEN EmptyZSeq ELSE [i \in ZIndices(s) |-> s[(i + r) % ZLen(s)]]

\* The set of all rotations of zero-indexed sequence s
Rotations(s) == IF s = EmptyZSeq THEN {} ELSE {[shift |-> r, seq   |-> Rotation(s, r)] : r \in ZIndices(s)}

===============================================================================
(* MV CONSTANT declarations *)
CONSTANTS 
    L = L,
    P1 = P1,
    P2 = P2,
    P3 = P3
  
(* MV CONSTANT definitions *)
CONSTANT
    Procs <- const_1633116534008310000
    
(* CONSTANT definitions *)
CONSTANT
    Edges <- const_1633116534008311000
    
CONSTANT
    Leader <- const<｜begin▁of▁sentence｜>3120000
  
(* CONSTRAINT definition *)
CONSTRAINT
    constr_1633116534008313000

(* SPECIFICATION definition *)
SPECIFICATION
    Spec
    
CHECK_DEADLOCK
    FALSE

(* INVARIANT definition *)
INVARIANT
    TypeOK,
    DT1Inv
  
(* PROPERTY definition *)
PROPERTY
    DT2

PROPERTIES  
    CountersConsistent,
    TreeWithRoot,
    (* StableUpEdge *)
    
(* Generated on Fri Oct 01 12:28:54 PDT 2021 *)
===============================================================================