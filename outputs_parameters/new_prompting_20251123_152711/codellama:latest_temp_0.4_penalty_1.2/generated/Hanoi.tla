---- MODULE Hanoi ----
(*****************************************************************************)
(* Tower of Hanoi with N towers.                                              *)
(*****************************************************************************)
CONSTANTS   D,     \* The number of disks.
            N,     \* The number of towers.
            big,   \* The tower containing the largest disk.
            small  \* The tower containing the smallest disk.
VARIABLES   rightTower,    \* The set of all towers with the largest disk.
            leftTower,     \* The set of all towers with the second-largest disk.
            midTower       \* The set of all towers with the third-largest disk.
VARIABLES   tower,         \* A tower containing a sequence of disks.
            disk          \* A single disk.
INVARIANT  NotSolved ==    \* An invariant that determines if we have found a solution or not.
                /\ (rightTower = {1} <-> D = N)      \* The right tower must contain the largest number of disks, iff all towers are full.
            /\ (leftTower = {} <-> N > 2)             \* If there is only one disk on a tower, it cannot be the left-most tower.
            /\ (midTower = {1} <-> D = N)        \* The middle tower must contain the second-largest number of disks, iff all towers are full.
            /\ (tower[i] = {} <-> i > 2)           \* If there is only one disk on a tower, it cannot be any other tower than the left-most and right-most ones.
            /\ (disk[1..D] = {})                   \* The set of disks must contain all numbers from 1 to D.
INVARIANT  TowerConstraints ==    \* An invariant that ensures every disk is on a valid tower.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskConstraints ==    \* An invariant that ensures the sum of disks on each tower does not exceed D.
                /\ (SUM[i | i \in DOMAIN tower] tower = D)   \* The total number of disks must be equal to D.
INVARIANT  TowerOrder ==    \* An invariant that ensures the order of the towers is correct.
                /\ (tower[1..N-2] < tower[3])      \* The leftmost and rightmost towers cannot have a smaller number of disks than any other tower in between them.
            /\ (tower[i+1] >= tower[i])              \* All towers must be ordered from smallest to largest.
INVARIANT  DiskOrder ==    \* An invariant that ensures the order of the disks on each tower is correct.
                /\ (DOMAIN tower = {})               \* The set of disks in a tower cannot be empty.
            /\ (disk[1..D] <= disk[2])              \* All disks must be ordered from smallest to largest.
INVARIANT  NotLessThanZero ==    \* An invariant that ensures every number is not less than zero.
                /\ (N >= 0)                         \* The number of towers cannot be negative.
            /\ (D >= 0)                             \* The total number of disks cannot be negative.
INVARIANT  TowerConstraints2 ==    \* An invariant that ensures every disk is on a valid tower, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskConstraints2 ==    \* An invariant that ensures the sum of disks on each tower does not exceed D, and the order of the disks on each tower is correct.
                /\ (SUM[i | i \in DOMAIN tower] tower = D)   \* The total number of disks must be equal to D.
            /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
INVARIANT  TowerOrder2 ==    * An invariant that ensures every tower has at least one disk, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskOrder2 ==    * An invariant that ensures every disk has a valid value, and the order of the disks on each tower is correct.
                /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
            /\ (disk[i] >= 0 <-> i > D-N+1)          \* If there are more than N-1 disks, then all disk values must be greater or equal to zero.
INVARIANT  NotLessThanZero2 ==    * An invariant that ensures every number is not less than zero.
                /\ (N >= 0)                         \* The number of towers cannot be negative.
            /\ (D >= 0)                             \* The total number of disks cannot be negative.
INVARIANT  TowerConstraints3 ==    * An invariant that ensures every disk is on a valid tower, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskConstraints3 ==    * An invariant that ensures the sum of disks on each tower does not exceed D, and the order of the disks on each tower is correct.
                /\ (SUM[i | i \in DOMAIN tower] tower = D)   \* The total number of disks must be equal to D.
            /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
INVARIANT  TowerOrder3 ==    * An invariant that ensures every tower has at least one disk, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskOrder3 ==    * An invariant that ensures every disk has a valid value, and the order of the disks on each tower is correct.
                /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
            /\ (disk[i] >= 0 <-> i > D-N+1)          \* If there are more than N-1 disks, then all disk values must be greater or equal to zero.
INVARIANT  NotLessThanZero3 ==    * An invariant that ensures every number is not less than zero.
                /\ (N >= 0)                         \* The number of towers cannot be negative.
            /\ (D >= 0)                             \* The total number of disks cannot be negative.
INVARIANT  TowerConstraints4 ==    * An invariant that ensures every disk is on a valid tower, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskConstraints4 ==    * An invariant that ensures the sum of disks on each tower does not exceed D, and the order of the disks on each tower is correct.
                /\ (SUM[i | i \in DOMAIN tower] tower = D)   \* The total number of disks must be equal to D.
            /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
INVARIANT  TowerOrder4 ==    * An invariant that ensures every tower has at least one disk, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskOrder4 ==    * An invariant that ensures every disk has a valid value, and the order of the disks on each tower is correct.
                /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
            /\ (disk[i] >= 0 <-> i > D-N+1)          \* If there are more than N-1 disks, then all disk values must be greater or equal to zero.
INVARIANT  NotLessThanZero4 ==    * An invariant that ensures every number is not less than zero.
                /\ (N >= 0)                         \* The number of towers cannot be negative.
            /\ (D >= 0)                             \* The total number of disks cannot be negative.
INVARIANT  TowerConstraints5 ==    * An invariant that ensures every disk is on a valid tower, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskConstraints5 ==    * An invariant that ensures the sum of disks on each tower does not exceed D, and the order of the disks on each tower is correct.
                /\ (SUM[i | i \in DOMAIN tower] tower = D)   \* The total number of disks must be equal to D.
            /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
INVARIANT  TowerOrder5 ==    * An invariant that ensures every tower has at least one disk, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskOrder5 ==    * An invariant that ensures every disk has a valid value, and the order of the disks on each tower is correct.
                /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
            /\ (disk[i] >= 0 <-> i > D-N+1)          \* If there are more than N-1 disks, then all disk values must be greater or equal to zero.
INVARIANT  NotLessThanZero5 ==    * An invariant that ensures every number is not less than zero.
                /\ (N >= 0)                         \* The number of towers cannot be negative.
            /\ (D >= 0)                             \* The total number of disks cannot be negative.
INVARIANT  TowerConstraints6 ==    * An invariant that ensures every disk is on a valid tower, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskConstraints6 ==    * An invariant that ensures the sum of disks on each tower does not exceed D, and the order of the disks on each tower is correct.
                /\ (SUM[i | i \in DOMAIN tower] tower = D)   \* The total number of disks must be equal to D.
            /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
INVARIANT  TowerOrder6 ==    * An invariant that ensures every tower has at least one disk, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskOrder6 ==    * An invariant that ensures every disk has a valid value, and the order of the disks on each tower is correct.
                /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
            /\ (disk[i] >= 0 <-> i > D-N+1)          \* If there are more than N-1 disks, then all disk values must be greater or equal to zero.
INVARIANT  NotLessThanZero6 ==    * An invariant that ensures every number is not less than zero.
                /\ (N >= 0)                         \* The number of towers cannot be negative.
            /\ (D >= 0)                             \* The total number of disks cannot be negative.
INVARIANT  TowerConstraints7 ==    * An invariant that ensures every disk is on a valid tower, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskConstraints7 ==    * An invariant that ensures the sum of disks on each tower does not exceed D, and the order of the disks on each tower is correct.
                /\ (SUM[i | i \in DOMAIN tower] tower = D)   \* The total number of disks must be equal to D.
            /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
INVARIANT  TowerOrder7 ==    * An invariant that ensures every tower has at least one disk, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskOrder7 ==    * An invariant that ensures every disk has a valid value, and the order of the disks on each tower is correct.
                /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
            /\ (disk[i] >= 0 <-> i > D-N+1)          \* If there are more than N-1 disks, then all disk values must be greater or equal to zero.
INVARIANT  NotLessThanZero7 ==    * An invariant that ensures every number is not less than zero.
                /\ (N >= 0)                         \* The number of towers cannot be negative.
            /\ (D >= 0)                             \* The total number of disks cannot be negative.
INVARIANT  TowerConstraints8 ==    * An invariant that ensures every disk is on a valid tower, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskConstraints8 ==    * An invariant that ensures the sum of disks on each tower does not exceed D, and the order of the disks on each tower is correct.
                /\ (SUM[i | i \in DOMAIN tower] tower = D)   \* The total number of disks must be equal to D.
            /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
INVARIANT  TowerOrder8 ==    * An invariant that ensures every tower has at least one disk, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskOrder8 ==    * An invariant that ensures every disk has a valid value, and the order of the disks on each tower is correct.
                /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
            /\ (disk[i] >= 0 <-> i > D-N+1)          \* If there are more than N-1 disks, then all disk values must be greater or equal to zero.
INVARIANT  NotLessThanZero8 ==    * An invariant that ensures every number is not less than zero.
                /\ (N >= 0)                         \* The number of towers cannot be negative.
            /\ (D >= 0)                             \* The total number of disks cannot be negative.
INVARIANT  TowerConstraints9 ==    * An invariant that ensures every disk is on a valid tower, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskConstraints9 ==    * An invariant that ensures the sum of disks on each tower does not exceed D, and the order of the disks on each tower is correct.
                /\ (SUM[i | i \in DOMAIN tower] tower = D)   \* The total number of disks must be equal to D.
            /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
INVARIANT  TowerOrder9 ==    * An invariant that ensures every tower has at least one disk, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskOrder9 ==    * An invariant that ensures every disk has a valid value, and the order of the disks on each tower is correct.
                /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
            /\ (disk[i] >= 0 <-> i > D-N+1)          \* If there are more than N-1 disks, then all disk values must be greater or equal to zero.
INVARIANT  NotLessThanZero9 ==    * An invariant that ensures every number is not less than zero.
                /\ (N >= 0)                         \* The number of towers cannot be negative.
            /\ (D >= 0)                             \* The total number of disks cannot be negative.
INVARIANT  TowerConstraints10 ==   * An invariant that ensures every disk is on a valid tower, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskConstraints10 ==   * An invariant that ensures the sum of disks on each tower does not exceed D, and the order of the disks on each tower is correct.
                /\ (SUM[i | i \in DOMAIN tower] tower = D)   \* The total number of disks must be equal to D.
            /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
INVARIANT  TowerOrder10 ==    * An invariant that ensures every tower has at least one disk, and the order of the towers is correct.
                /\ (tower[i] = {} <-> i > N)        \* If there are no more than N-1 disks, then the set of towers must be smaller or equal to {1..N}.
            /\ (DOMAIN tower <= 2^D - 1)           \* The number of towers is bounded by 2^D.
INVARIANT  DiskOrder10 ==    * An invariant that ensures every disk has a valid value, and the order of the disks on each tower is correct.
                /\ (DOMAIN disk <= 2^D - 1)             \* The set of disks cannot exceed the maximum value allowed by a natural number.
            /\ (disk[i] >= 0 <-> i > D-N+1)          \* If there are more than N-1 disks, then all disk values must be greater or equal to zero.
INVARIANT  NotLessThanZero10 ==   * An invariant that ensures every number is not less than zero.
                /\ (N >= 0)                         \* The number of towers cannot be negative.
            /\ (D >= 0)                             \* The total number of disks cannot be negative.
====