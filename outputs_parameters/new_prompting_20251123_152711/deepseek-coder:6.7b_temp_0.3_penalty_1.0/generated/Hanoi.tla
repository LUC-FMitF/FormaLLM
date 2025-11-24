---- MODULE Hanoi ----
MODULE Hanoi

-- Constants and Variables
CONSTANTS D, N, Tower, Disk
VARIABLES towers, disks, moves

-- Initial State
Init ==
    /\ towers = [0 .. N-1] -> {}
    /\ disks = [1 .. 2^D]
    /\ moves = 0

-- Predicates
EmptyTower(tower) ==
    /\ tower \in towers
    /\ towers[tower] = {}

DiskOnTower(disk, tower) ==
    /\ tower \in towers
    /\ disk \in towers[tower]

SmallestDiskOnTower(disk, tower) ==
    /\ tower \in towers
    /\ towers[tower] = {disk}

CanMoveOff(disk, tower) ==
    /\ tower \in towers
    /\ disk \in towers[tower]
    /\ ~EmptyTower(tower)

CanMoveTo(disk, tower) ==
    /\ tower \in towers
    /\ disk \in disks
    /\ ~DiskOnTower(disk, tower)
    /\ ~EmptyTower(tower)
    /\ ~CanMoveOff(DISK'[tower], tower)

-- Next State
Next ==
    [] CanMoveTo(disk, tower)
    [] CanMoveOff(disk, tower)
    [] CanMoveTo(DISK'[tower], tower')
    [] CanMoveOff(DISK'[tower], tower')
    [] moves' = moves + 1

-- Specification
Spec ==
    [] << towers, disks, moves >> INIT
    [] ~EmptyTower(tower) -> tower \in towers
    [] ~DiskOnTower(disk, tower) -> disk \in towers[tower]
    [] ~SmallestDiskOnTower(disk, tower) -> tower \in towers /\ towers[tower] = {disk}
    [] ~CanMoveOff(disk, tower) -> tower \in towers /\ disk \in towers[tower]
    [] ~CanMoveTo(disk, tower) -> tower \in towers /\ disk \in disks /\ ~DiskOnTower(disk, tower) /\ ~EmptyTower(tower)
    [] ~Next -> <<towers', disks', moves'>> INSTANCEOF Hanoi

-- Invariant
Inv_rightTower ==
    [] towers[N-1] = disks

END MODULE
====