---- MODULE Hanoi ----

(***************************************************************************)
(* Towers of Hanoi with N towers                                            *)
(***************************************************************************)

EXTENDS Bags, Powerset, Sequences -- Import the standard libraries for bags, powerset and sequences.

CONSTANTS   D, N  \* D is number of disks and N number of towers.
VARIABLES   towers, moves

\* Initial predicate: Set up initial configuration with all disks on the first tower.
Init ==
    /\ towers[i] = [0 .. i-1] FORALL i \in 0..D-1  \* All towers are empty except the first one which has all disks.
    /\ moves = 0                                                  \* Initially, no moves have been made.

\* Operator for moving a disk from one tower to another: Move(fromTower, toTower)
Move(fromTower, toTower) ==
    [i \in 0..D-1 | (towers[i] = fromTower \setminus {MaxElement(fromTower)}) FOR i \in 0..N-1]  -- Update the towers.
    /\ moves' = moves + 1                                                     -- Increment number of moves.

\* Actions that disks can perform: Push and Pop operations on towers.
Push(toTower, disk) == [i \in 0..D-1 | (towers[i] = toTower U {disk}) FOR i \in 0..N-1] -- Add a disk to the top of a tower.
Pop(fromTower) == [i \in 0..D-1 | (towers[i] = fromTower \setminus {MaxElement(fromTower)}) FOR i \in 0..N-1] -- Remove the topmost disk from a tower.

\* Specification of Hanoi problem: Begins in Init, and every step either satisfies Next or leaves <<big, small>> unchanged.
Spec == [Init] ++ {Move(fromTower, toTower) : (towers[0], towers[1]) \in {(Powerset[D](Nat), Powerset[D](Nat))} - Move(fromTower, toTower)}
====