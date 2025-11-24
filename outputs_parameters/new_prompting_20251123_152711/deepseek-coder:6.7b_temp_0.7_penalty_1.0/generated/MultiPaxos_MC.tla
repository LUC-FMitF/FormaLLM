---- MODULE MultiPaxos_MC ----


EXTENDS Module

CONSTANTS 
    Replicas = {s1, s2, s3}
    Writes = {w1, w2}
    Reads = {r1}
    MaxBallot = ConstMaxBallot

VARIABLES
    state[Replicas]

ASSUMPTIONS
    Init == state = [r \in Replicas |-> InitState]
    Next == [s \in Replicas |-> IF s = s1 THEN NextState1 ELSE NextState2]

SPECIFICATION
    [Init]<>[Next]_<<state>>

INVARIANTS
    TypeOK == \E r \in Replicas : state[r] \in ReplicableState
    Linearizability == \E r \in Replicas : state[r] = LinearizableState

TLC_CONFIGURATION
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

---- END OF MODULE ReplicatedStateMachine ----
====