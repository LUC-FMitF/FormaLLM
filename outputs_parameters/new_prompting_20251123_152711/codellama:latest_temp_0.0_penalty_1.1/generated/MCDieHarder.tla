---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal     \* The goal value for the game.
    == 4

Jug      \* The capacity of the jug.
    <- MCJug

Capacity \* The function that maps a value of Jug to its capacity.
    <- MCCapacity

Spec ==
    Init /\ [][Next]_<<Goal, Jug, Capacity>>

INVARIANTS TypeOK NotSolved

=============================================================================
====