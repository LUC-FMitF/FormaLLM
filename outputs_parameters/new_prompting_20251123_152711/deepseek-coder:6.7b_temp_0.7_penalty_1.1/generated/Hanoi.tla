---- MODULE Hanoi ----
CONSTANTS
  D = 3, (* Number of disks *)
  N = 3; (* Number of towers *)

INVARIANTS
  == rightTower, (* Invariant checking all disks are on the rightmost tower *)

EXTEND
  == NotSolved; (* Search for unsolved configurations *)
====