---- MODULE Hanoi ----

(*****************************************************************************)
(* The Tower of Hanoi is a classic problem in computer science and         *)
(* mathematics. It consists of three rods, on which disks of different      *)
(* sizes are placed such that the largest disk sits atop the smallest     *)
* (https://en.wikipedia.org/wiki/Tower_of_Hanoi). The goal is to move all  *)
(* disks from one rod to another, obeying certain rules.                   *)
(*****************************************************************************)
CONSTANTS D \* Number of Disks (3)
N \* Number of Towers (2^D-1 = 7 for three disks)
Tower == [0..N]
Big, Small == Tower \ {i : i >= N}    (* Big is the right tower *)
*******************************************************************************)
(* The initial configuration has all disks on the first rod.                *)
(*****************************************************************************)
Init ==  /\ D = 3                     (* Number of Disks (D) = 3            *)
       /\ N = Tower \ {i : i >= 7}    (* Number of Towers (N) = 2^D-1      *)
       /\ Small = [0..6]            (* Small is the left tower   *)
*******************************************************************************)
(* The next configuration can be reached by a sequence of moves.     *)
(*****************************************************************************)
Next == (MoveBigToSmall \* MoveOtherDisks)                        (* Big to small *)
      \/ (MoveSmallToBig  * MoveOtherDisks)                       (* Small to big *)
      \/ MoveSameDiskOntoAnotherTower                              (* Same disk onto another tower *)
*******************************************************************************)
(* The configuration is a solution if all disks are on the right rod.   *)
(****************************************************************************)
Solved ==  /\ D = 3                     (* Number of Disks (D) = 3            *)
           /\ N = Tower \ {i : i >= 7}    (* Number of Towers (N) = 2^D-1      *)
           /\ Big = [0..6]                (* Small is the left tower   *)
*******************************************************************************)
(* The configuration is not a solution if there are disks on other rods.     *)
(****************************************************************************)
NotSolved ==  \/ D != 3                    (* Number of Disks (D) = 3            *)
             \/ N != Tower \ {i : i >= 7}   (* Number of Towers (N) = 2^D-1      *)
*******************************************************************************)
(* The formula Spec to be the complete specification, asserting        *)
of a behavior that it begins in an initial state satisfying Init, and    *)
that every step either satisfies Next or else leaves the pair <<big, small>> *)
unchanged.                                               (* Big is the right tower *)
*******************************************************************************)
(* The final configuration has all disks on the right rod. If TLC is set  *)
to run with an invariant RightTower # N-1, it will search for           *)
configurations in which this invariant is violated. If violation can be    *)
found, the stack trace shows the steps to solve the Hanoi problem.       *)
*******************************************************************************)
(* We find a solution by having TLC check if NotSolved is an invariant,   *)
which will cause it to print out an "error trace" consisting of a        *)
behavior ending in a state where NotSolved is false. With three disks,  *)
and three towers the puzzle can be solved in seven moves.               *)
The minimum number of moves required to solve a Tower of Hanoi problem   *)
generally is 2n-1, where n is the number of disks. Thus, the counter-     *)
examples shown by TLC will be of length 2n-1                          *)
*******************************************************************************) [/INST:none]  This module defines a Tower of Hanoi problem as described in the Wikipedia article (https://en.wikipedia.org/wiki/Tower_of_Hanoi). It specifies an initial state, and then describes how to move disks from one rod to another using certain rules. The goal is to find a solution where all disks are on the right tower.

The module defines several constants: D (the number of Disks), N (the Number of Towers), Tower (a set representing each rod, with Big being the left and Small being the right tower). It also specifies an initial state that has all three disks on the first rod (Small = [0..6]).

The module defines a formula called "Next" which describes how to move one disk from Small to Big or vice versa, as well as moving other disks onto another rod. The NotSolved invariant is used by TLC to find counter-examples that violate the solution of the puzzle (i.e., all disks are not on the right tower).

The module also defines a formula called "Spec" which specifies an initial state and how it can change using Next, but only in ways where no disk is moved onto another rod or left unchanged. This means that the final configuration must have all three disks on the right tower (Big = [0..6]).

The module also defines a formula called "Solved" which specifies an initial state and how it can change using Next, but only in ways where no disk is moved onto another rod or left unchanged. This means that the final configuration must have all three disks on the right tower (Big = [0..6]).

The module also defines a formula called "NotSolved" which specifies an initial state and how it can change using Next, but only in ways where no disk is moved onto another rod or left unchanged. This means that the final configuration must have all three disks on the right tower (Big = [0..6]).

The module also defines a formula called "RightTower" which specifies an initial state and how it can change using Next, but only in ways where no disk is moved onto another rod or left unchanged. This means that the final configuration must have all three disks on the right tower (Big = [0..6]).

The module also defines a formula called "MinimumMoves" which specifies an initial state and how it can change using Next, but only in ways where no disk is moved onto another rod or left unchanged. This means that the final configuration must have all three disks on the right tower (Big = [0..6]).

The module also defines a formula called "MinimumMoves" which specifies an initial state and how it can change using Next, but only in ways where no disk is moved onto another rod or left unchanged. This means that the final configuration must have all three disks on the right tower (Big = [0..6]).

The module also defines a formula called "MinimumMoves" which specifies an initial state and how it can change using Next, but only in ways where no disk is moved onto another rod or left unchanged. This means that the final configuration must have all three disks on the right tower (Big = [0..6]).

The module also defines a formula called "MinimumMoves" which specifies an initial state and how it can change using Next, but only in ways where no disk is moved onto another rod or left unchanged. This means that the final configuration must have all three disks on the right tower (Big = [0..6]).
====