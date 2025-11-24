---- MODULE MajorityProof ----

(**************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ... , n-1}).                                             *)
(**************************************************************************)

CONSTANTS EmptyZSeq == {}

VARIABLES Sequences

EmptySequenceProperty == []EmptyZSeq = EmptyZSeq
LengthFunctionProperty == 
    \A s : Sequences -> ZLen(s) IN Naturals 
    /\ (\A n : Naturals -> ZSeqOfLength(S, n) SUBSET Sequences)

TypeOK == LengthFunctionProperty 
     /\ EmptySequenceProperty

ZIndexSubsetProperty == 
    \E s : Sequences -> ZIndices(s) SUBSET Naturals

AuxiliaryLemma1 ==  
    \A n : Naturals -> 
        Cardinality(ZSeqOfLength(S, n)) = n + 1
     /\ 0 NOTIN ZIndices(EmptyZSeq)
     /\ \A s : Sequences -> (ZLen(s) = 0) IFF (s = EmptyZSeq)

AuxiliaryLemma2 ==  
    \E n, m : Naturals -> 
        ZIndices([i IN 0..<n UNION 1+m..<n+m] -> S) = 
         [0..<n] UNION [m..<n+m]
     /\ \A s : Sequences, n : Natural -> 
        ZIndices(Rotation(s, n)) = { (i + n mod Cardinality(ZLen(s))) MOD Cardinality(ZLen(s)) : i IN ZIndices(s)}
     /\ \A s : Sequences -> Rotations(s) = 
         { [shift |->  r, seq |-> Rotation(s, r)] : r IN ZIndices(s)}

CorrectnessBasedOnInvariant ==  
    []ZSeq(S) = Sequences 
     /\ \A s : Sequences -> (ZLen(s) = 0) IFF (s = EmptyZSeq)
     /\ \A s, t : Sequences, n : Naturals -> 
        ((t IN ZSeqOfLength(S, Cardinality(s))) AND (Rotation(s, n) = t)) 
        IMPLIES (ZLen(s) = Cardinality(s) + n MOD Cardinality(s))
     /\ \A s : Sequences -> ZIndices(s) SUBSET Naturals 
     /\ []a:\preceq b == (ZLen(b) >= ZLen(a)) AND (([i IN ZIndices(a) |->  a[i] = b[i]] IMPLIES i < ZLen(a)))

Spec == CALLTYPEOK 
     /\ [][]AuxiliaryLemma1 
      /\ []ZSeq(S) = Sequences 
       /\ []AuxiliaryLemma2 
        /\ []CorrectnessBasedOnInvariant
        =============================================================================
        ====

TLC Configuration:
CONSTANTS EmptyZSeq = {}
           ZeroNatural = 0
INVARIANTS TypeOK, ZIndexSubsetProperty, AuxiliaryLemma1, AuxiliaryLemma2, CorrectnessBasedOnInvariant 
SPECIFICATION Spec
=============================================================================
        ====