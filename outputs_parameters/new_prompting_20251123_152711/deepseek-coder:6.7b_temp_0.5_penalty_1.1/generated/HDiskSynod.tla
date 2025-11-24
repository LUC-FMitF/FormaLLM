---- MODULE HDiskSynod ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of  *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ... , n-1}).                                             *)
(***************************************************************************)

EXTENDS TLC

CONSTANTS
    EmptySet == {}

VARIABLES
    Sequence <<>>

ASSIGN
    EmptyZSeq == <<>>,
    ZIndices(s) == IF s = EmptyZSeq THEN EmptySet ELSE DOMAIN s,
    ZSeqOfLength(S, n) == IF n = 0 THEN {EmptyZSeq} ELSE [0 .. (n - 1) -> S],
    ZSeq(S) == UNION {ZSeqOfLength(S, n): n \in N},
    ZLen(s) == IF s = EmptyZSeq THEN 0 ELSE Cardinality(DOMAIN s),
    ZSeqFromSeq(seq) == IF seq = EmptySet THEN EmptyZSeq ELSE [i IN 0..(Cardinality(seq)-1) -> seq[i]],
    SeqFromZSeq(zseq) == IF zseq = EmptyZSeq THEN EmptySet ELSE [i IN 1..ZLen(zseq) -> zseq[i-1]],
    a \preceq b == LET (s1len, s2len, IsLexLeq(_, _, _)) == (ZLen(a), ZLen(b), IsLexLeq(a, b, 0)) IN (s1len = s2len) /\ ((a[i] < b[i]) OR (a[i] > b[i])) AND (IsLexLeq(_, _, _) == IF (s1len = 0) OR (s2len = 0) THEN s1len <= s2len ELSE a[i] = b[i] AND IsLexLeq(_, _, _)),
    Rotation(s, r) == IF s = EmptyZSeq THEN EmptyZSeq ELSE [i IN ZIndices(s) -> s[(i + r) MOD ZLen(s)]],
    Rotations(s) == IF s = EmptyZSeq THEN {} ELSE {[shift, seq] : shift IN ZIndices(s), seq == Rotation(s, shift)}

INVARIANT
    TypeOK == SUBSET (DOMAIN Sequence, N),  (* Assuming Sequence is indexed by natural numbers *)
    LengthOK == EVERY i IN DOMAIN Sequence /\ ZLen(Sequence[i]) = Cardinality(DomainOf(Sequence[i])),
    ConversionOK == EVERY i IN DOMAIN Sequence /\ SeqFromZSeq(Sequence[i]) = Sequence[i] AND ZSeqFromSeq(Sequence[i]) = Sequence[i],
    RotationOK == EVERY i, j IN DOMAIN Sequence /\ (FORALL k IN 0..ZLen(Sequence[j]) -> Rotation(Sequence[i], k) = Sequence[j]),
    OrderOK == FORALL a, b IN ZSeq(UNIVERSE OF Sequence) /\ a \preceq b IMPLIES EXISTS r IN N /\ (FORALL i IN 0..ZLen(a)-1 -> a[i+r MOD ZLen(a)] = b[i]),
    EmptyOK == ZSeqFromSeq(EmptySet) = EmptyZSeq AND SeqFromZSeq(EmptyZSeq) = EmptySet

SPECIFICATION
    Spec1 == [](TypeOK /\ LengthOK /\ ConversionOK /\ RotationOK /\ OrderOK /\ EmptyOK),
    Init == INITIALIZATION {Sequence}[],
    Next == [](Sequence' = Append(Sequence, ZSeqFromSeq({UNIVERSE OF Sequence})[0]) AFTER {} UNION {[i |-> Rotation(Sequence[i], 1)] : i IN DOMAIN Sequence}),
    Trans == [](Next)

TLCCONFIG
    +VERBOSE,
    +TRIM,
    +LIMITCOUNTEREXAMPLELENGTH=80,
    +SPECFILENAME="ZSequences.tla",
    +INVARIANTFILENAME="Invariants_ZSequences.txt",
    -PERSISTENTMODULUS=1000000007,
    -LANGUAGE="ANSI-C",
    -TIMER=5000,
    +STATEFILENAME="state_ZSequences.txt"
=============================================================================
====