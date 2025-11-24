---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.   *)
(**************************************************************************)

CONSTANTS Goal     \* The goal to reach.
    == 4

CONSTANTS Jug      \* The number of gallons in the jug.
    == 3

CONSTANTS Capacity \* The capacity of the jug.
    == 4

Spec ==
    /\ Goal = Capacity
    /\ Goal = Jug

NotSolved ==
    /\ \A t \in 0..3 : t \notin {0, 1, 2}

TypeOK ==
    /\ Goal \in Nat
    /\ Jug \in Nat
    /\ Capacity \in Nat
    /\ [t \in 0..3 |-> t \in {0, 1, 2}]

MCJug ==
    [j \in 0..3 |->
        IF j = 0
        THEN 0
        ELSE IF j = 1
        THEN 1
        ELSE 2
    ]

MCCapacity ==
    [j \in 0..3 |->
        IF j = 0
        THEN 0
        ELSE IF j = 1
        THEN 1
        ELSE 2
    ]

=============================================================================
====