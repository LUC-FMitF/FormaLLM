---- MODULE Hanoi ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 0..(n-1)  *)
(* (the set {0, 1, ... , n-1}).                                            *)
(***************************************************************************)
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

CONSTANTS  D, N  \* The number of disks and towers respectively.
VARIABLES  big, small  \* The indices for the big and small tower.
CONSTANTS  DISK_ON_TOWER  \* The predicate that a disk is on a given tower.
FUNCTION   ZSeq(S)  \* The set of all zero-indexed sequences of elements in S with length n.
FUNCTION   ZLen(s)  \* The length of zero-indexed sequence s.
FUNCTION   ZSeqFromSeq(seq)  \* Converts from a one-indexed sequence to a zero-indexed sequence.
FUNCTION   SeqFromZSeq(zseq)  \* Converts from a zero-indexed sequence to a one-indexed sequence.
CONSTANTS  ZIndices(s)  \* The set of valid indices for zero-indexed sequence s.
INVARIANT  NotSolved  \* An invariant that will cause TLC to print an "error trace" if violated.

INITIALISATION
================
Init ==
  LET
    DisksOnTower(t) ==
      IF t = EmptyZSeq
      THEN {}
      ELSE {i \in ZIndices(s) |-> s[i] = t}
  IN
    (* all towers are empty except all disks are on the first Tower *)
    DisksOnTower(big) == DOMAIN DISK_ON_TOWER
    AND NOT EXISTS i \in ZIndices(small) | DisksOnTower(i)
    (* All less significant bits are 0 *)
    small < (2^D - 1)
    (* Remaining tower does not change *)
    TOWERS[i \in D..N-1] == i

Next
==========
Next ==
  LET
    DisksOnTower(t) ==
      IF t = EmptyZSeq
      THEN {}
      ELSE {i \in ZIndices(s) |-> s[i] = t}
  IN
    (* Move smallest disk on big tower to the remaining tower. *)
    [smallest, big] < DisksOnTower(big)
    -> NOT EXISTS j \in ZIndices(remaining) | DisksOnTower(j)
    -> DisksOnTower(big)[smallest] = remaining
    (* Move smallest disk on small tower to the remaining tower. *)
    [smallest, small] < DisksOnTower(small)
    -> NOT EXISTS j \in ZIndices(remaining) | DisksOnTower(j)
    -> DisksOnTower(small)[smallest] = remaining
    (* Move smallest disk on remaining tower to the big tower. *)
    [smallest, remaining] < DisksOnTower(remaining)
    -> NOT EXISTS j \in ZIndices(big) | DisksOnTower(j)
    -> DisksOnTower(remaining)[smallest] = big
    (* No need to try to move onto the same tower (Move(...) prevents it too) *)
    [i, i] < DisksOnTower(i) -> FALSE
    (* Modification History
    Last modified Tue May 17 14:55:33 CEST 2016 by markus
    Created Sun Jul 17 10:20:57 CEST 2011 by markus *)
  IN TRUE

NotSolved ==
  LET
    AllOnTower(t) ==
      IF t = EmptyZSeq
      THEN {}
      ELSE {i \in ZIndices(s) |-> s[i] = t}
  IN NOT EXISTS i \in 1..D-1 | AllOnTower(i) # (2^D - 1)
====