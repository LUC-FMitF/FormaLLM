---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)
CONSTANTS Goal = 4                   \* The goal of each player is to      *)
                                \* capture or destroy all enemy soldiers.*)
VARIABLES Jug, Capacity            \* A jug has a capacity and can hold    *)
                                \* any number of soldiers.               *)
-----------------------------------------------------------------------------
MCJug == [j |-> j >= 0]             \* The value of the jug is nonnegative.*)
MCCapacity(j) == IF j = MCJug THEN   \* A function that returns a capacity*)
                    Capacity         \* for each possible value of Jug. *)
-----------------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Goal, Jug>>  \* The initial state is the goal     *)
                                \* and an empty jug.                      *)
Init == Goal = 4 /\ Jug = MCJug        \* In this case, we have a single   *)
-----------------------------------------------------------------------------
Next == [Goal' |-> IF Goal > Capacity THEN Capacity ELSE Goal]    \* soldier.*)
                                \/ [Jug' |-> (IF Jug = MCJug THEN 0 ELSE Jug - 1)]
TypeOK == /\ Goal >= 4 ==> GOAL IN {2,3}   \* The goal is either 2 or 3. *)
-----------------------------------------------------------------------------
NotSolved ==                        \* This invariant states that the game*)
    IF (Goal = 0) THEN TRUE ELSE FALSE     \* has not been solved yet.      *)
=============================================================================