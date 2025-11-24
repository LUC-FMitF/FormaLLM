---- MODULE Hanoi ----
(**************************************************************************)
(* Towers of Hanoi with N towers                                          *)
(* Each tower is represented by a natural number, all towers are empty      *)
(* except all disks are on the first Tower.                                *)
(* All less significant bits are 0.                                        *)
(* Remaining tower does not change.                                        *)
(* No need to try to move onto the same tower (Move(...) prevents it too). *)
(* Modification History                                                    *)
(* Last modified Tue May 17 14:55:33 CEST 2016 by markus                  *)
(* Created Sun Jul 17 10:20:57 CEST 2011 by markus                        *)
(**************************************************************************)

CONSTANTS
  Domain == {0, 1}
  N == 3 (* Number of towers *)
  D == 3 (* Number of disks *)

ASSIGNABLE VARIABLES
  Towers[0 .. N-1] == {0} (* Towers are represented by natural numbers, all towers are empty except all disks are on the first Tower *)
  Disks == {0 .. D-1} (* Disks are represented by natural numbers *)

OPERATIONS
  IsEmpty(tower) == EMPTYSET == Towers[tower]
  IsNotEmpty(tower) == NOT EMPTYSET == Towers[tower]
  IsOnTower(disk, tower) == disk IN Towers[tower]
  IsSmallestOnTower(disk, tower) == MINIMUM(Towers[tower]) == disk
  CanMoveOff(disk, tower) == IsOnTower(disk, tower) AND IsNotEmpty(tower)
  CanMoveTo(disk, tower) == NOT IsOnTower(disk, tower) AND IsNotEmpty(tower)

OPERATIONS
  Move(disk, from, to) ==
    IF CanMoveOff(disk, from) AND CanMoveTo(disk, to)
    THEN Towers[from] \ disk / Towers[to] \ disk
    ELSE .

INVARIANTS
  rightTower == \x : x IN Towers[N-1] : x
  NotSolved == EXISTS {disk} (EXISTS {from, to} (CanMoveOff(disk, from) AND CanMoveTo(disk, to)))

Next == .

SPECIFICATION
  Init == .
  Spec == .

=============================================================================
====