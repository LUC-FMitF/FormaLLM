---- MODULE MultiPaxos_MC ----
/*
 * TLC configuration-related defs
 */

CONSTANTS
    Replicas = {s1, s2, s3}
    Writes = {w1, w2}
    Reads = {r1}
    MaxBallot = ConstMaxBallot

SPECIFICATION Spec

/*
 * Linearizability constraint
 */

CHECK_DEADLOCK TRUE

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

/*
 * Type check invariant
 */

INVARIANTS
    TypeOK
    Linearizability

/*
 * Definitions
 */

EMPTY 
    ZeroSeq

/*
 * Valid indices for zero-indexed sequences
 */

ZIndices(s) 
    IF s = ZeroSeq
    THEN {}
    ELSE DOMAIN s

/*
 * All zero-indexed sequences of elements in S with length n
 */

ZSeqOfLength(S, n) 
    IF n = 0
    THEN {ZeroSeq}
    ELSE [0..(n-1) -> S]

/*
 * All zero-indexed sequences of elements in S
 */

ZSeq(S) 
    UNION {ZSeqOfLength(S, n) : n IN Nat}

/*
 * Length of zero-indexed sequence s
 */

ZLen(s) 
    IF s = ZeroSeq
    THEN 0
    ELSE Cardinality(DOMAIN s)

/*
 * Converts from a one-indexed sequence to a zero-indexed sequence
 */

ZSeqFromSeq(seq) 
    IF seq = ZeroSeq
    THEN ZeroSeq
    ELSE [i -> seq[(i + 1) MOD ZLen(seq)]]

/*
 * Converts from a zero-indexed sequence to a one-indexed sequence
 */

SeqFromZSeq(zseq) 
    IF zseq = ZeroSeq
    THEN ZeroSeq
    ELSE [i -> zseq[(i - 1) MOD ZLen(zseq)]]

/*
 * Lexicographic order on zero-indexed sequences a and b
 */

a precelib(b) 
    LET
        s1len = ZLen(a)
        s2len = ZLen(b)
        RECURSIVE IsLexLeq(_, _, _)
        IsLexLeq(s1, s2, i) 
          = CASE i = s1len / i = s2len -> s1len <= s2len
            [] s1[i] < s2[i] -> TRUE
            [] s1[i] > s2[i] -> FALSE
            [] OTHER -> IsLexLeq(s1, s2, i + 1)
    IN IsLexLeq(a, b, 0)

/*
 * Rotate the string s to the left by r indices
 */

Rotation(s, r) 
    IF s = ZeroSeq
    THEN ZeroSeq
    ELSE [i -> s[(i + r) MOD ZLen(s)]]

/*
 * The set of all rotations of zero-indexed sequence s
 */

Rotations(s) 
    IF s = ZeroSeq
    THEN {}
    ELSE [{
        shift |-> r,
        seq    |-> Rotation(s, r)
       } : r IN ZIndices(s)]

END
====