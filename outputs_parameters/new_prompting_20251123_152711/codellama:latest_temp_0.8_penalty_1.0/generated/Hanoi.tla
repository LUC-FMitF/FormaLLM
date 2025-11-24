---- MODULE Hanoi ----

(***************************************************************************)
(* Towers of Hanoi with N towers                                         *)
(***************************************************************************)
CONSTANTS   D,       \* The number of disks in the system.                *)
            N,       \* The number of towers.                             *)
            bigTower,    \* The tower with the largest disk.               *)
            smallTower,  \* The tower with the smallest disk.              *)
            notSmall,   \* A set of all disks that are not on the small   *)
                       \* tower.                                           *)
VARIABLES   big,    \* The number of disks on the big tower.               *)
            small,   \* The number of disks on the small tower.            *)
            disks,   \* The set of all disks in the system.                *)
            towers  \* A data structure representing the state of the     *)
                      \* towers.                                           *)
----------------------------------------------------------------------------
\* The number of disks in the system. *
D == 3

\* The number of towers. *
N == 3

\* The tower with the largest disk. *
bigTower == 1

\* The tower with the smallest disk. *
smallTower == 3

\* A set of all disks that are not on the small tower. *
notSmall == {1, 2, 4}

\* The number of disks on the big tower. *
big == D - N + 1

\* The number of disks on the small tower. *
small == N - D + 1

\* The set of all disks in the system. *
disks == {1..D}

\* A data structure representing the state of the towers. *
towers == {{bigTower..big}, {notSmall}, {smallTower..small}}

=============================================================================
====