---- MODULE EWD687a_anim --------------------------------------------------------

CONSTANTS
    EmptyZSeq = <<>>
    NodesOfNetwork = {L, P1, P2, P3, P4, P5}
    Network = LET Edgs = SUBSET { n \in (NodesOfNetwork \X NodesOfNetwork):
        n[1] # n[2]
    } IN TLCEval(RandomElement(Edgs))

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) ==
    IF s = EmptyZSeq
    THEN {}
    ELSE DOMAIN s

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
        s1len = ZLen(a)
        s2len = ZLen(b)
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

CONSTANT
    Procs <- NodesOfNetwork

CONSTANT
    Edges <- Network

CONSTANT
    Leader <- L

SPECIFICATION
    Spec

INVARIANT
    TypeOK
    DT1Inv
    InterestingBehavior

PROPERTY
    DT2
    CountersConsistent
    TreeWithRoot
    StableUpEdge

ALIAS
    Alias

CHECK_DEADLOCK
    FALSE

ACTION_CONSTRAINT
    NoSuperfluousIdleSteps

=============================================================================
====