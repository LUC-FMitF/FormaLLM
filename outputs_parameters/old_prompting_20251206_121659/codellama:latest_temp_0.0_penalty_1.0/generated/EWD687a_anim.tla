---- MODULE EWD687a_anim ----
EXTENDS Naturals, Sequences

CONSTANT
    EmptyZSeq == <<>>

CONSTANT
    ZIndices(s) ==
        IF s = EmptyZSeq
        THEN {}
        ELSE DOMAIN s

CONSTANT
    ZSeqOfLength(S, n) ==
        IF n = 0
        THEN {EmptyZSeq}
        ELSE [0 .. (n - 1) -> S]

CONSTANT
    ZSeq(S) == UNION {ZSeqOfLength(S, n) : n \in Nat}

CONSTANT
    ZLen(s) ==
        IF s = EmptyZSeq
        THEN 0
        ELSE Cardinality(DOMAIN s)

CONSTANT
    ZSeqFromSeq(seq) ==
        IF seq = <<>>
        THEN EmptyZSeq
        ELSE [i \in 0..(Len(seq)-1) |-> seq[i+1]]

CONSTANT
    SeqFromZSeq(zseq) ==
        IF zseq = EmptyZSeq
        THEN <<>>
        ELSE [i \in 1..ZLen(zseq) |-> zseq[i-1]]

CONSTANT
    a \preceq b ==
        LET
            s1len == ZLen(a)
            s2len == ZLen(b)
            RECURSIVE IsLexLeq(_, _, _)
            IsLexLeq(s1, s2, i) ==
                CASE i = s1len \/ i = s2len -> s1len <= s2len
                [] s1[i] < s2[i] -> TRUE
                [] s1[i] > s2[i] -> FALSE
                [] OTHER -> IsLexLeq(s1, s2, i + 1)
        IN IsLexLeq(a, b, 0)

CONSTANT
    Rotation(s, r) ==
        IF s = EmptyZSeq
        THEN EmptyZSeq
        ELSE [i \in ZIndices(s) |-> s[(i + r) % ZLen(s)]]

CONSTANT
    Rotations(s) ==
        IF s = EmptyZSeq
        THEN {}
        ELSE {[
            shift |-> r,
            seq   |-> Rotation(s, r)
        ] : r \in ZIndices(s)
        }

SPECIFICATION
    Init == TRUE

Next ==
    LET
        s == [i \in ZIndices(msgs) |-> msgs[i]]
        r == [i \in ZIndices(acks) |-> acks[i]]
    IN
        IF s = EmptyZSeq
        THEN
            IF r = EmptyZSeq
            THEN TRUE
            ELSE FALSE
        ELSE
            IF r = EmptyZSeq
            THEN FALSE
            ELSE
                IF s \preceq r
                THEN TRUE
                ELSE FALSE

INVARIANT
    TypeOK ==
        LET
            s == [i \in ZIndices(msgs) |-> msgs[i]]
            r == [i \in ZIndices(acks) |-> acks[i]]
        IN
            IF s = EmptyZSeq
            THEN
                IF r = EmptyZSeq
                THEN TRUE
                ELSE FALSE
            ELSE
                IF r = EmptyZSeq
                THEN FALSE
                ELSE
                    IF s \preceq r
                    THEN TRUE
                    ELSE FALSE

INVARIANT
    DT1Inv ==
        LET
            s == [i \in ZIndices(msgs) |-> msgs[i]]
            r == [i \in ZIndices(acks) |-> acks[i]]
        IN
            IF s = EmptyZSeq
            THEN
                IF r = EmptyZSeq
                THEN TRUE
                ELSE FALSE
            ELSE
                IF r = EmptyZSeq
                THEN FALSE
                ELSE
                    IF s \preceq r
                    THEN TRUE
                    ELSE FALSE

INVARIANT
    InterestingBehavior ==
        LET
            s == [i \in ZIndices(msgs) |-> msgs[i]]
            r == [i \in ZIndices(acks) |-> acks[i]]
        IN
            IF s = EmptyZSeq
            THEN
                IF r = EmptyZSeq
                THEN TRUE
                ELSE FALSE
            ELSE
                IF r = EmptyZSeq
                THEN FALSE
                ELSE
                    IF s \preceq r
                    THEN TRUE
                    ELSE FALSE

PROPERTY
    DT2 ==
        LET
            s == [i \in ZIndices(msgs) |-> msgs[i]]
            r == [i \in ZIndices(acks) |-> acks[i]]
        IN
            IF s = EmptyZSeq
            THEN
                IF r = EmptyZSeq
                THEN TRUE
                ELSE FALSE
            ELSE
                IF r = EmptyZSeq
                THEN FALSE
                ELSE
                    IF s \preceq r
                    THEN TRUE
                    ELSE FALSE

ALIAS
    Alias ==
        LET
            s == [i \in ZIndices(msgs) |-> msgs[i]]
            r == [i \in ZIndices(acks) |-> acks[i]]
        IN
            IF s = EmptyZSeq
            THEN
                IF r = EmptyZSeq
                THEN TRUE
                ELSE FALSE
            ELSE
                IF r = EmptyZSeq
                THEN FALSE
                ELSE
                    IF s \preceq r
                    THEN TRUE
                    ELSE FALSE

CHECK_DEADLOCK
    FALSE

ACTION_CONSTRAINT
    NoSuperfluousIdleSteps ==
        LET
            s == [i \in ZIndices(msgs) |-> msgs[i]]
            r == [i \in ZIndices(acks) |-> acks[i]]
        IN
            IF s = EmptyZSeq
            THEN
                IF r = EmptyZSeq
                THEN TRUE
                ELSE FALSE
            ELSE
                IF r = EmptyZSeq
                THEN FALSE
                ELSE
                    IF s \preceq r
                    THEN TRUE
                    ELSE FALSE
====