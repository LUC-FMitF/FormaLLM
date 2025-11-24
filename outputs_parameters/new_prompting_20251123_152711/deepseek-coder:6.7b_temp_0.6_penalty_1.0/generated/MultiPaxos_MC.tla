---- MODULE MultiPaxos_MC ----


CONSTANTS
    State = {A, B}

VARIABLES
    CurrentState \in State

ASSIGN
    Initial ==
        CurrentState = A

NextState ==
    \E s \in State : s' = IF CurrentState = A THEN B ELSE A

Spec ==
    [](CurrentState = A) /\ [](CurrentState = B)

Invariants ==
    TypeOK

SPECIFICATION Spec

INVARIANTS
    TypeOK == CurrentState \in State

TLC Configuration:

SPECIFICATION Spec

CONSTANTS
    Replicas = {s1, s2, s3}
    Writes = {w1, w2}
    Reads = {r1}
    MaxBallot = ConstMaxBallot

SYMMETRY SymmetricPerms

INVARIANTS
    TypeOK
    Linearizability

CHECK_DEADLOCK TRUE
=============================================================================
====