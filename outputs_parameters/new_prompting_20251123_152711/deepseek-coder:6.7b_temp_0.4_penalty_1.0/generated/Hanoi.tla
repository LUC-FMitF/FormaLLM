---- MODULE Hanoi ----

CONSTANTS  N, D, Empty, NotEmpty
VARIABLES  Towers, Disk, Move

ASSUME 
  N \in \mathbb{N} \setminus \{0\},
  D \in \mathbb{N},
  Disk \subseteq \{0, 1, ..., 2^D - 1\},
  Towers \subseteq \mathbb{N}^N,
  Move \subseteq Towers \times Disk,
  Empty == 0,
  NotEmpty == 1,
  TowersInit == [n \in N |-> IF n = 0 THEN Empty ELSE NotEmpty],
  DiskInit == [d \in 0..2^D - 1]

DEFINE
  Move(tower, disk) ==
    [n \in 0..N - 1 |-> IF n = tower THEN disk ELSE Towers[n]],
  IsEmpty(tower) == Towers[tower] = Empty,
  IsNotEmpty(tower) == Towers[tower] = NotEmpty,
  TopDisk(tower) == IF IsNotEmpty(tower) THEN MAX(Disk : Disk \in Towers[tower]) ELSE Empty,
  CanMoveOff(tower, disk) == IsNotEmpty(tower) AND TopDisk(tower) = disk,
  CanMoveOn(tower, disk) == IsEmpty(tower) OR TopDisk(tower) > disk

INVARIANT
  rightTower == SUM(d \in Disk |-> IF d \in Towers[N - 1] THEN 1 ELSE 0)

NEXT
  IF EXISTS tower \in N : CanMoveOff(tower, TopDisk(tower)) AND EXISTS next \in N : CanMoveOn(next, TopDisk(tower))
  THEN [n \in N |-> IF n = tower THEN Towers[next] ELSE IF n = next THEN Move(tower, TopDisk(tower)) ELSE Towers[n]]
  ELSE <<>>

SPECIFICATION
  Init == <<Towers>> = TowersInit, <<Disk>> = DiskInit,
  Next == [Towers', Disk'] == <<Towers>>' = Towers', <<Disk>>' = Disk',
  Spec == Init /\ WFRec(Next)

TLC CONFIGURATION
  InvMode == "OneError"

=============================================================================
====