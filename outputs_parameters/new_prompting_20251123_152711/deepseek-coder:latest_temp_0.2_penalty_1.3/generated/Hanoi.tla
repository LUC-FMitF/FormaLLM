---- MODULE Hanoi ----
MODULE TowersOfHanoi

CONSTANTS D, N, NotSolved

VARIABLES Towers, Disk, Move

INITIAL 
  Towers = [0..N-1]
  Disk = 0
  Move = False

ACTION Init
  IF Towers = [0..N-1]
  THEN Disk = 0
  ELSE Disk = N

ACTION MoveDisk
  IF Towers[Disk] = N
  THEN Move = False
  ELSE
    IF Towers[Disk] > 0
    THEN Towers[Disk] = Towers[Disk] + 1
    ELSE Towers[Disk] = 0
    Move = True

ACTION MoveDiskToTower
  IF Towers[Disk] = N
  THEN Move = False
  ELSE
    IF Towers[Disk] > 0
    THEN Towers[Disk] = Towers[Disk] + 1
    ELSE Towers[Disk] = 0
    Move = True

ACTION Next
  IF Disk = N
  THEN IF Towers[N] = N
  THEN Disk = N - 1
  ELSE Towers[N] = 0
  Move = True

ACTION Solve
  IF NotSolved
  THEN Disk = N
  ELSE Disk = 0

ACTION CheckInvariant
  IF NotSolved
  THEN Disk = N

INVARIANT RightTower
  IF Towers = [0..N-1]
  THEN RightTower = True
  ELSE RightTower = False

END TowersOfHanoi
====