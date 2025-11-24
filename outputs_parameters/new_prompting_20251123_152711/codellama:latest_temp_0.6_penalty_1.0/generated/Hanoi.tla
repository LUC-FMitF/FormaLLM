---- MODULE Hanoi ----

(*****************************************************************************)
(* The Tower of Hanoi is a classic problem in computer science. It involves  *)
(* moving disks from one tower to another, subject to certain rules.         *)
(*                                                                          *)
(* In this module we define the initial predicate and the specification     *)
(* that asserts the behavior of the Towers of Hanoi puzzle. The solution    *)
(* consists in moving all disks from one tower to another, following a       *)
(* specific sequence of moves.                                            *)
(*****************************************************************************)
CONSTANTS   D, N           \* Number of disks and number of towers.
VARIABLES   big, small     \* Tower where the disk is located.
            NotSolved      \* Invariant: all disks are on the right tower.
------------------------------------------------------------------------------
Disc ==    \* A disc in a tower.
    [tower |-> TOWER]  \* The tower where it is located.
    [disk   |-> DISK ]  \* The disk itself.
    
Tower ==    \* A tower with disks on top of each other, from bottom to top.*
    [discs |-> {Disc}]  \* Set of discs in the tower.
------------------------------------------------------------------------------
Init ==      (* Initial predicate *)
   ALL i: Nat | i < D -> big = N - (i + 1) & small = 0
==============================================================================
Next ==       (* Specification for behavior *)
    [big, small] \in {(tower, tower') : tower' >= tower}
                     /\ NotSolved => <<big', small'>> # <<big, small>>
------------------------------------------------------------------------------
NotSolved ==  ALL i: Nat | i < D -> big = N - (i + 1) & small = i + 1
==============================================================================
*)
*****************************************************************************
The initial predicate specifies the starting position of the disks, *)
(* where all disks are on the first tower and no disk is on top of    *)
(* another.                                                            *)
(**************************************************************************)
INIT ==      (* Initial predicate *)
   ALL i: Nat | i < D -> big = N - (i + 1) & small = 0
==============================================================================
Next ==       (* Specification for behavior *)
    [big, small] \in {(tower, tower') : tower' >= tower}
                     /\ NotSolved => <<big', small'>> # <<big, small>>
------------------------------------------------------------------------------
NotSolved ==  ALL i: Nat | i < D -> big = N - (i + 1) & small = i + 1
==============================================================================
*)
*****************************************************************************
The specification for the behavior of the Towers of Hanoi puzzle is *)
(* that every step either satisfies Next or leaves the pair <<big,   *)
(* small>> unchanged.                                                *)
(**************************************************************************)
==============================================================================
NotSolved ==  ALL i: Nat | i < D -> big = N - (i + 1) & small = i + 1
==============================================================================
*)
*****************************************************************************
The final configuration has all disks on the right tower. If TLC is set *)
(* to run with an invariant rightTower # 2^N-1, it will search for     *)
(* configurations in which this invariant is violated. If violation can be*)
(* found, the stack trace shows the steps to solve the Hanoi problem.   *)
(**************************************************************************)
==============================================================================
NotSolved ==  ALL i: Nat | i < D -> big = N - (i + 1) & small = i + 1
==============================================================================
*)
*****************************************************************************
The minimum number of moves required to solve a Tower of Hanoi puzzle   *)
(* generally is 2n-1, where n is the number of disks. Thus, the counter- *)
(* examples shown by TLC will be of length 2n-1                        *)
(**************************************************************************)
==============================================================================
NotSolved ==  ALL i: Nat | i < D -> big = N - (i + 1) & small = i + 1
==============================================================================
*)
====