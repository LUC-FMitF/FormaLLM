---- MODULE Hanoi ----
EXTENDS Bags, Integers  -- Import standard library modules.

(**************************************************************************)
(* Defines the Tower of Hanoi problem with N towers                          *)
(**************************************************************************)
CONSTANTS   D \* Number of disks,
            N \* Number of towers.
VARIABLES   Towers[N],  -- Represents each tower as a bag of disk sizes.
            DiskSize[D]  -- Size (1-indexed power of two) for each disk.
ASSUME      D > 0,     -- At least one disk is required to play the game.
            2^(Cardinality(\{i | i \in Domain(DiskSize), DiskSize[i]\})) = Cardinality(Domain(Towers))  -- Each tower must contain a different number of disks (power-of-two sizes).
OPERATOR    Move(t, d) == IF t /= {} AND Head(t) > d THEN {Head(t)} + Tail(t) ELSE t END. -- Operator to move disk from one tower to another if possible.
INVARIANT   rightTower \* 2^N - Cardinality(\{i | i \in Domain(DiskSize), DiskSum[i] = Towers[\{\varnothing\} + Range(Domain(Towers))]\}) == 0 -- Invariant to check if all disks are on the last tower.
OPERATOR    NotSolved == IF Cardinality(\{i | i \in Domain(DiskSize), DiskSum[i] = Towers[\{\varnothing\} + Range(Domain(Towers))]\}) > 0 THEN TRUE ELSE FALSE END -- Operator to check if the puzzle is not solved yet.
INVARIANT   NotSolved == IF Cardinality(\{i | i \in Domain(DiskSize), DiskSum[i] = Towers[\{\varnothing\} + Range(Domain(Towers))]\}) > 0 THEN TRUE ELSE FALSE END -- Invariant to check if the puzzle is not solved yet.
OPERATOR    Init == [n ∈ N |-> IF n = 1 THEN {DiskSize[d]} ELSE {} END] -- Initial state of towers with one disk on each tower (except for first).
ASSUME      Towers[\{\varnothing\} + Range(Domain(Towers))] = Init,  -- All disks are initially in the leftmost tower.
            DiskSize[d] = 2^d FORALL d \in Domain(DiskSize),   -- Each disk is a power of two (1-indexed).
            0 < Cardinality(\{i | i \in Domain(Towers)}) = N,  -- Number of towers must be at least one.
            D > 2^N - 1 FORALL n \in Domain(DiskSize),   -- Total number of disks should not exceed total possible tower count (minus one).
            0 < Cardinality(\{i | i \in Domain(Towers)}) = N,  -- Number of towers must be at least one.
            D > 2^N - 1 FORALL n \in Domain(DiskSize)   -- Total number of disks should not exceed total possible tower count (minus one).
OPERATOR    Next == [n ∈ N |-> IF Head(\{i | i \in Domain(Towers), Towers[i] = {} OR DiskSum[Head(Towers)] > d}) THEN Move(Towers[\{\varnothing\} + Range({0,1} - {n})], n) ELSE Tower END]. -- Next state of towers after a move.
OPERATOR    Spec == IF Cardinality(\{i | i \in Domain(DiskSize), DiskSum[i] = Towers[\{\varnothing\} + Range(Domain(Towers))]\}) > 0 THEN TRUE ELSE FALSE END -- Complete specification of the game behavior.
====