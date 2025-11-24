---- MODULE MCDieHarder ----

(***************************************************************************)
(* The following definitions duplicate the original Die Hard problem. *)
(***************************************************************************)

CONSTANTS Jug, Capacity, Goal

VARIABLES Jug, Capacity

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

EmptyZSeq == <<>>

ZIndices(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE DOMAIN s

ZSeqOfLength(S, n) ==
  IF n = 0
  THEN {EmptyZSeq}
  ELSE [0 .. (n - 1) -> S]

ZSeq(S) == UNION {ZSeqOfLength(S, n) : n IN Nat}

ZLen(s) ==
  IF s = EmptyZSeq
  THEN 0
  ELSE Cardinality(DOMAIN s)

ZSeqFromSeq(seq) ==
  IF seq = <<>>
  THEN EmptyZSeq
  ELSE [i IN 0 .. (Len(seq) - 1) |-> seq[i + 1]]

SeqFromZSeq(zseq) ==
  IF zseq = EmptyZSeq
  THEN <<>>
  ELSE [i IN 1 .. ZLen(zseq) |-> zseq[i - 1]]

a preceq b ==
  LET
    s1len == ZLen(a)
    s2len == ZLen(b)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len / i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(a, b, 0)

Rotation(s, r) ==
  IF s = EmptyZSeq
  THEN EmptyZSeq
  ELSE [i IN ZIndices(s) |-> s[(i + r) % ZLen(s)]]

Rotations(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE [
      shift |-> r,
      seq   |-> Rotation(s, r)
     ] : r IN ZIndices(s)

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 0..(n-1)   *)
(* (the set {0, 1, ..., n-1}).                                             *)
(***************************************************************************)

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

EmptyZSeq == <<>>

ZIndices(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE DOMAIN s

ZSeqOfLength(S, n) ==
  IF n = 0
  THEN {EmptyZSeq}
  ELSE [0 .. (n - 1) -> S]

ZSeq(S) == UNION {ZSeqOfLength(S, n) : n IN Nat}

ZLen(s) ==
  IF s = EmptyZSeq
  THEN 0
  ELSE Cardinality(DOMAIN s)

ZSeqFromSeq(seq) ==
  IF seq = <<>>
  THEN EmptyZSeq
  ELSE [i IN 0 .. (Len(seq) - 1) |-> seq[i + 1]]

SeqFromZSeq(zseq) ==
  IF zseq = EmptyZSeq
  THEN <<>>
  ELSE [i IN 1 .. ZLen(zseq) |-> zseq[i - 1]]

---- TLC Configuration ----
(***************************************************************************)
(* To have TLC find a solution, we must tell it what values to use for the  *)
(* constant parameters Jug, Capacity, and Goal. However, TLC does not      *)
(* allow one to write function-valued expressions in a configuration file.  *)
(* So, we use this module, which extends module DieHarder, to define a function *)
(* MCCapacity and have the configuration file TLC to substitute MCCapacity for *)
(* Capacity. Since we need to know the value of Jug to define Capacity (which *)
(* is a function having Jug as its domain), we also define MCJug and tell TLC *)
(* to substitute it for Jug.                                                 *)
(***************************************************************************)

CONSTANTS Goal = MCGoal
          Jug = MCJug
          Capacity = MCCapacity

SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
====