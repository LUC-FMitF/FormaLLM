---- MODULE MCDieHarder --------

(***************************************************************************)
(* The following definitions duplicate the original Die Hard problem. *)
(***************************************************************************)

CONSTANTS Jug, Capacity, Goal

VARIABLES MCJug, MCCapacity

INITIAL 
  Jug = MCJug
  Capacity = MCCapacity

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module extends module DieHarder to define a function MCCapacity and *)
(* have the configuration file TLC to substitute MCCapacity for Capacity. *)
(* Since we need to know the value of Jug to define Capacity, we also define *)
(* MCJug and tell TLC to substitute it for Jug. *)
(***************************************************************************)

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

EmptyZSeq == 
  []

ZIndices(s) ==
  IF s = EmptyZSeq
  THEN 
    {}
  ELSE 
    DOMAIN s

ZSeqOfLength(S, n) 
  IF n = 0
  THEN 
    EmptyZSeq
  ELSE 
    [i ∈ 0..(n - 1) |-> S[i + 1]]

ZSeq(S) 
  UNION 
    {ZSeqOfLength(S, n) : n ∈ Nat}

ZLen(s) 
  IF s = EmptyZSeq
  THEN 
    0
  ELSE 
    Cardinality(DOMAIN s)

ZSeqFromSeq(seq) 
  IF seq = EmptyZSeq
  THEN 
    EmptyZSeq
  ELSE 
    [i ∈ 1..ZLen(seq) |-> seq[i - 1]]

SeqFromZSeq(zseq) 
  IF zseq = EmptyZSeq
  THEN 
    EmptyZSeq
  ELSE 
    [i ∈ 0..(ZLen(zseq) - 1) |-> zseq[(i + 1) % ZLen(zseq)]]

a 
  Precedes b 
  LET
    s1len 
    IF s1 = EmptyZSeq
    THEN 
      0
    ELSE 
      Cardinality(DOMAIN s1)
    s2len 
    IF s2 = EmptyZSeq
    THEN 
      0
    ELSE 
      Cardinality(DOMAIN s2)
    RECURSIVE 
      IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) 
      CASE 
        i = s1len 
        OR i = s2len 
        -> s1len <= s2len
        [] s1[i] < s2[i] 
        -> FALSE
        [] s1[i] > s2[i] 
        -> FALSE
        [] OTHER 
        -> IsLexLeq(s1, s2, i + 1)
  IN 
    IsLexLeq(a, b, 0)

Rotation(s, r) 
  IF s = EmptyZSeq
  THEN 
    EmptyZSeq
  ELSE 
    [i ∈ ZIndices(s) |-> s[(i + r) % ZLen(s)]]

Rotations(s) 
  IF s = EmptyZSeq
  THEN 
    {}
  ELSE 
    [{
      shift 
      ∈ 
        ZIndices(s)
      seq 
      ∈ 
        Rotation(s, shift)
    } : shift ∈ Nat]

(***************************************************************************)
(* This module extends module DieHarder to define a function MCCapacity and *)
(* have the configuration file TLC to substitute MCCapacity for Capacity. *)
(* Since we need to know the value of Jug to define Capacity, we also define *)
(* MCJug and tell TLC to substitute it for Jug. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module extends module DieHarder to define a function MCJug and *)
(* have the configuration file TLC to substitute MCJug for Jug. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the configuration file for TLC. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved

(***************************************************************************)
(* This module is the TLC configuration file. *)
(***************************************************************************)

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
====