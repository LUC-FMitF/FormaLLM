---- MODULE HDiskSynod ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ... , n-1}).                                             *)
(***************************************************************************)

EXTENDS TLC

CONSTANTS S = {...} \* The set of all elements in S.
            FiniteSets, Naturals, Sequences : Module
            
\* The empty zero-indexed sequence
EmptyZSeq == [x: x NOTIN DOMAIN 0..(n - 1) |-> TRUE] \* for any n >= 0 in Nat.

\* The set of valid indices for zero-indexed sequence s
ZIndices[s](n, m : Naturals) == 
    IF Cardinality(DOMAIN s) > n THEN DOMAIN (s EXCEPT [x: x NOTIN 0..m |-> TRUE]) ELSE {}
    
\* The set of all zero-indexed sequences of elements in S with length n
ZSeqOfLength[n](seq : Sequences, s) == IF Cardinality(DOMAIN seq) > n THEN DOMAIN (s EXCEPT [x: x NOTIN 0..(Cardinality(DOMAIN seq)-1) |-> TRUE]) ELSE {}
    
\* The set of all zero-indexed sequences of elements in S
ZSeq[seq](n : Naturals, s : Sequences, ss: FiniteSetOfOneElem) == 
    UNION { ZSeqOfLength(ss)[x]: x NOTIN 0..Cardinality(DOMAIN seq)-1 |-> TRUE}
    
\* The length of zero-indexed sequence s
ZLen[s](n : Naturals, m: FiniteSet) ==  IF Cardinality(DOMAIN s) > n THEN (Dom - Domain([x: x NOTIN 0..m |-> TRUE])) ELSE {}
    
\* Converts from a one-indexed sequence to a zero-indexed sequence
ZSeqFromOneIndex[s](n : Naturals, m : FiniteSet) ==  [i \in ZIndices(DOMAIN s)[0..Cardinality(Dom)-1] |-> (IF i > 0 THEN Domain([x: x NOTIN 0..m |-> TRUE]) ELSE FALSE)]
    
\* Converts from a zero-indexed sequence to a one-indexed sequence
OneIndexFromZSeq[s](n : Naturals, m : FiniteSet) ==  [i \in ZIndices(DOMAIN s)[0..Cardinality(Dom)-1] |-> (IF i > 0 THEN Domain([x: x NOTIN <｜begin▁of▁sentence｜>[(i+m)]]) ELSE FALSE)]
    
\* Lexicographic order on zero-indexed sequences a and b
aPreceqb[s, t](n : Naturals) ==  [i \in ZIndices(DOMAIN s)[0..Cardinality(Dom)-1] |-> (IF i = Cardinality([x: x NOTIN 0..(LengthOfDomain - n)])) THEN TRUE ELSE FALSE
    
\* Rotate the string s to the left by r indices
Rotation[s](r : Naturals, m : FiniteSet) ==  [i \in ZIndices(DOMAIN s)[0..Cardinality(Dom)-1] |-> (IF i + Cardinality([x: x NOTIN 0..m]) > LengthOfDomain THEN Domain([x: x NOTIN <｜begin▁of▁sentence｜>[(i+r) % m ]])) ELSE FALSE)]
    
\* The set of all rotations of zero-indexed sequence s
Rotation[s](n : Naturals, r : FiniteSet) ==  UNION { Rotation(ss)[x]: x NOTIN 0..Cardinality([i: i NOTIN ZIndices(DOMAIN ss)])}
    
SPECIFICATION == ([]EmptyZSeq /\ []Rotations[s] \/ [](aPreceqb) )    (* Specification for the module *)
====