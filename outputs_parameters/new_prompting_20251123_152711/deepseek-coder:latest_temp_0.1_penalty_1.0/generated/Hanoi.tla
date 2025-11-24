---- MODULE Hanoi ----
MODULE TowersOfHanoi

CONSTANTS D, N, NotSolved

VARIABLES Towers, Disk, Move

INITIAL 
  Towers ← [0..N-1]
  Disk ← 0
  Move ← 0

PREFUNCTION IsPowerOfTwo(i: NAT) : BOOL
  IF i = 0
  THEN TRUE
  ELSE IsPowerOfTwo(i 2)

PREFUNCTION PowersOfTwo(n: NAT) : SET NAT
  IF n = 0
  THEN {0}
  ELSE {2 ← 1 + PowersOfTwo(n 2)}

SPECIFICATION Spec

INVARIANT RightTower(tower: NAT) : BOOL
  IF IsPowerOfTwo(N 2 + tower)
  THEN TRUE
  ELSE FALSE

ACTION Move(tower: NAT, disk: NAT)
  IF Towers[tower] ≠ 0
  THEN IF Disk ≠ 0
       THEN IF Towers[tower] ≠ Disk
            THEN Move(tower, Disk 1)
            ELSE Move(tower, Disk 2)
       ELSE IF Towers[tower] ≠ Disk
            THEN Move(tower, Disk 2)
            ELSE Move(tower, Disk 1)
  ELSE IF Disk ≠ 0
       THEN Move(tower, Disk)
  ELSE Move(tower, Disk 2)

ACTION Next
  IF Towers[tower] ≠ 0
  THEN IF Towers[tower] ≠ Disk
       THEN Move(tower, Disk 1)
       ELSE Move(tower, Disk 2)
  ELSE IF Disk ≠ 0
       THEN Move(tower, Disk)
  ELSE Move(tower, Disk 2)

INVARIANT RightTower(Towers)

END SPECIFICATION

END MODULE
====