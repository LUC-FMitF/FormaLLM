------------------------------- MODULE Hanoi -------------------------------
EXTENDS Naturals, Bits, FiniteSets, TLC

PowerOfTwo(i) == i & (i-1) = 0

SetOfPowerOfTwo(n) == {x \in 1..(2^n-1): PowerOfTwo(x)}

Sum(f) == LET DSum[S \in SUBSET DOMAIN f] ==
LET elt == CHOOSE e \in S : TRUE
IN  IF S = {} THEN 0
ELSE f[elt] + DSum[S \ {elt}]
IN  DSum[DOMAIN f]

CONSTANT D, N

VARIABLES towers
vars == <<towers>>

Inv == Sum(towers) = 2^D - 1

TypeOK == /\ \A i \in DOMAIN towers : /\ towers[i] \in Nat
/\ towers[i] < 2^D

Init == /\ towers = [i \in 1..N |-> IF i = 1 THEN 2^D - 1 ELSE 0]

IsEmptyTower(tower) == tower = 0

IsOnTower(tower, disk) == /\ tower & disk = disk

IsSmallestDisk(tower, disk) == /\ IsOnTower(tower, disk)
/\ tower & (disk - 1) = 0

CanMoveOff(tower, disk) == /\ IsOnTower(tower, disk)
/\ IsSmallestDisk(tower, disk)

CanMoveTo(tower, disk) == \/ tower & (disk - 1) = 0
\/ IsEmptyTower(tower)

Move(from, to, disk) == /\ CanMoveOff(towers[from], disk)
/\ CanMoveTo(towers[to], disk)
/\ towers' = [towers EXCEPT ![from] = towers[from] - disk,
![to] = towers[to] + disk]

Next == \E d \in SetOfPowerOfTwo(D): \E idx1, idx2 \in DOMAIN towers:
/\ idx1 # idx2
/\ Move(idx1, idx2, d)

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------

NotSolved == towers[N] # 2^D - 1

=============================================================================
