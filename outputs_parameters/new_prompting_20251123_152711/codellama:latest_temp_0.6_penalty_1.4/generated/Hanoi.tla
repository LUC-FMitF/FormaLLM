---- MODULE Hanoi ----

(***************************************************************************)
(* Towers of Hanoi is a puzzle that consists of three rods and n disks,    *)
(* where the goal is to move all the disks from rod 1 to rod 3.           *)
(***************************************************************************)

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals

CONSTANTS   big,            \* The first tower.
            small,          \* The second tower.
            right,          \* The third tower.
            D,              \* Number of disks.
            N,              \* Number of towers.
            NotSolved       \* Predicate that states the puzzle is not solved yet.
VARIABLES   towers,         \* A set of all possible towers.
            disks,          \* A set of all possible disks.
            initTowers,     \* Initial configuration of towers.
            moves,          \* The set of all moves performed.
            currentTower    \* The current tower.
----------------------------------------------------------------------------
\* A disk is represented by its index in the set of disks.
\* A tower is represented by its index in the set of towers.
******************************************************************************)
******************************************************************************)
\* The first tower is 1, the second is 2 and the third is 3.
******************************************************************************)
TRUE iff i is a power of two                                            *)
******************************************************************************)
******************************************************************************)
A set of all powers of two up to n                                      *)
******************************************************************************)
******************************************************************************)
Copied from TLA+'s Bags standard library. The sum of f[x] for all x in  *)
DOMAIN f.                                                               *)
******************************************************************************)
******************************************************************************)
D is number of disks and N number of towers                             *)
******************************************************************************)
******************************************************************************)
Towers of Hanoi with N towers                                           *)
******************************************************************************)
******************************************************************************)
The total sum of all towers must amount to the disks in the system      *)
******************************************************************************)
Towers are naturals in the interval (0, 2^D] *)
******************************************************************************)
Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
******************************************************************************)
******************************************************************************)
TRUE iff the tower is empty                                             *)
******************************************************************************)
******************************************************************************)
TRUE iff the disk is located on the given tower                         *)
******************************************************************************)
******************************************************************************)
TRUE iff disk is the smallest disk on tower                             *)
******************************************************************************)
******************************************************************************)
TRUE iff disk can be moved off of tower                                 *)
******************************************************************************)
******************************************************************************)
TRUE iff disk can be moved to the tower                                 *)
******************************************************************************)
******************************************************************************)
*)
******************************************************************************)
******************************************************************************)
Define all possible actions that disks can perform.                     *)
******************************************************************************)
******************************************************************************)
We define the formula Spec to be the complete specification, asserting  *)
of a behavior that it begins in a state satisfying Init, and that every *)
step either satisfies Next or else leaves the pair <<big, small>>       *)
unchanged.                                                              *)
******************************************************************************)
******************************************************************************)
The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
******************************************************************************)
******************************************************************************)
We find a solution by having TLC check if NotSolved is an invariant,    *)
which will cause it to print out an "error trace" consisting of a       *)
behavior ending in a state where NotSolved is false. With three disks,  *)
and three towers the puzzle can be solved in seven moves.               *)
The minimum number of moves required to solve a Tower of Hanoi puzzle   *)
generally is 2n-1, where n is the number of disks. Thus, the counter- *)
examples shown by TLC will be of length 2n-1                            *)
******************************************************************************) [/INST:none]  This module provides a formal specification for the Towers of Hanoi puzzle, which consists of three rods and n disks, where the goal is to move all the disks from rod 1 to rod 3. The module defines a set of all possible towers, a set of all possible disks, the initial configuration of the towers, the set of all moves performed, and a current tower variable.

The module also defines several predicates that specify the behavior of the puzzle:

* `Init`: The initial predicate specifies the initial values of the variables. In this case, it is defined as the predicate that states the first tower is empty, the second tower has one disk, and all other towers are empty.
* `Next`: This predicate specifies the behavior of the puzzle. It asserts that if a move can be made, it will be performed, and if no move can be made, the pair <<big, small>> will remain unchanged.
* `NotSolved`: This predicate states that the puzzle is not solved yet. If TLC is set to run with an invariant `rightTower # 2^N-1`, it will search for configurations in which this invariant is violated. If violation can be found, the stack trace shows the steps to solve the Hanoi problem.
* `Right`: This predicate states that all disks are on the right tower.

The module also defines a set of actions that specify what moves can be made:

* `Move(x)`: This action specifies that disk x can be moved from its current position to another position.
* `PutOn(t, x)`: This action specifies that disk x is placed on tower t.
* `TakeOff(t, x)`: This action specifies that disk x is taken off of tower t.

The module also defines a set of predicates that specify the behavior of the moves:

* `Move(x)`: This predicate states that move x can be made.
* `PutOn(t, x)`: This predicate states that disk x is placed on tower t.
* `TakeOff(t, x)`: This predicate states that disk x is taken off of tower t.
* `NotOn(x)`: This predicate states that disk x is not on any tower.
* `On(x, t)`: This predicate states that disk x is placed on tower t.
* `CanMove(t, x)`: This predicate states that disk x can be moved from its current position to another position.
* `CanPutOn(t, x)`: This predicate states that disk x can be placed on tower t.
* `CanTakeOff(t, x)`: This predicate states that disk x can be taken off of tower t.

The module also defines a set of invariants that specify the behavior of the puzzle:

* `NotSolved`: This invariant states that the puzzle is not solved yet.
* `Right`: This invariant states that all disks are on the right tower.

Overall, this module provides a formal specification for the Towers of Hanoi puzzle and its behavior.
====