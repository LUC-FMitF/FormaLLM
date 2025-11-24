---- MODULE Hanoi ----

(*****************************************************************************)
(* The Towers of Hanoi is a classic problem in computer science and         *)
(* mathematics. It consists of three rods, and n disks of different       *)
(* sizes. The goal is to move all the disks from one rod to another while  *)
(* following certain rules.                                               *)
(*****************************************************************************)
CONSTANTS   D, N, bigTower, smallTower, rightTower, leftTower,            \* The number of disks and the two rods.
            disk1, disk2, ..., diskN,                                    \* The individual disks.
            tower1, tower2, ..., towerN                                  \* The individual towers.
VARIABLES   big, small,                                                  \* The current state of the two rods.
            moves                                                         \* A log of all moves made so far.
-----------------------------------------------------------------------------
Init ==    /\ D > N                                                      \* Ensure that there are enough disks to move.
          /\ big = 2^N - 1                                               \* The initial state is the tower with all disks on it.
          /\ small = 0                                                \* The other tower starts empty.
          /\ moves = <<>>                                            \* No moves have been made yet.
=============================================================================
Next ==    [big, small] -> Next'                                   \* Move a disk from the big rod to the small rod.
           [small, big] -> Next'                                   \* Move a disk from the small rod to the big rod.
           [tower1, tower2, ..., towerN] -> Next'                  \* Move a disk from one tower to another.
=============================================================================
NotSolved == /\ moves = <<>>                                        \* The puzzle is solved if no moves have been made yet.
             /\ big != rightTower                                   \* Ensure that the final configuration has all disks on the right tower.
=============================================================================
Spec ==    Init /\ [](Next) => NotSolved                           \* The specification is satisfied if the initial state satisfies Init and every step either satisfies Next or leaves the pair <<big, small>> unchanged.
=============================================================================
TLC config:                                                          *)
**************************************************************************)
\* Set the invariant to be rightTower # 2^N-1                     *)
\* This will cause TLC to search for configurations in which this   *)
\* invariant is violated. If violation can be found, the stack trace*)
\* shows the steps to solve the Hanoi problem.                      *)
**************************************************************************)
\* The minimum number of moves required to solve a Tower of Hanoi  *)
\* puzzle generally is 2n-1, where n is the number of disks. Thus,*)
\* the counter-examples shown by TLC will be of length 2n-1        *)
**************************************************************************) [/INST:ref]  // This is an example specification for TowersOfHanoi problem in TLA+.
// The spec states that there are three rods and n disks, where n > D.
CONSTANTS   D, N, bigTower, smallTower, rightTower, leftTower,            // The number of disks and the two rods.
            disk1, disk2, ..., diskN,                                    // The individual disks.
            tower1, tower2, ..., towerN                                  // The individual towers.
VARIABLES   big, small,                                                  // The current state of the two rods.
            moves                                                         // A log of all moves made so far.
=============================================================================
Init ==    /\ D > N                                                      // Ensure that there are enough disks to move.
          /\ big = 2^N - 1                                               // The initial state is the tower with all disks on it.
          /\ small = 0                                                \* The other tower starts empty.
          /\ moves = <<>>                                            \* No moves have been made yet.
=============================================================================
Next ==    [big, small] -> Next'                                   // Move a disk from the big rod to the small rod.
           [small, big] -> Next'                                   // Move a disk from the small rod to the big rod.
           [tower1, tower2, ..., towerN] -> Next'                  \* Move a disk from one tower to another.
=============================================================================
NotSolved == /\ moves = <<>>                                        // The puzzle is solved if no moves have been made yet.
             /\ big != rightTower                                   // Ensure that the final configuration has all disks on the right tower.
=============================================================================
Spec ==    Init /\ [](Next) => NotSolved                           \* The specification is satisfied if the initial state satisfies Init and every step either satisfies Next or leaves the pair <<big, small>> unchanged.
=============================================================================
TLC config:                                                          *)
**************************************************************************)
\* Set the invariant to be rightTower # 2^N-1                     *)
\* This will cause TLC to search for configurations in which this   *)
\* invariant is violated. If violation can be found, the stack trace*)
\* shows the steps to solve the Hanoi problem.                      *)
**************************************************************************)
\* The minimum number of moves required to solve a Tower of Hanoi  *)
\* puzzle generally is 2n-1, where n is the number of disks. Thus,*)
\* the counter-examples shown by TLC will be of length 2n-1        *)
**************************************************************************)
====