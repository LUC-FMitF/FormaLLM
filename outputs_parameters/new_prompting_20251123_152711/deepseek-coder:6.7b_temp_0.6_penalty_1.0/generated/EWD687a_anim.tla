---- MODULE EWD687a_anim ----------------------------------------------------

CONSTANTS
    L   = "Leader"
    P1  = "Process1"
    P2  = "Process2"
    P3  = "Process3"
    P4  = "Process4"
    P5  = "Process5"

CONSTANT
    NodesOfNetwork == {L, P1, P2, P3, P4, P5}

CONSTANT
    Network ==
        LET Edges == SUBSET 
            { n \in (NodesOfNetwork \X NodesOfNetwork) :
                \* No self-loops.
                /\ n[1] \# n[2]
                \* L is a source and never a sink.
                /\ n[2] \# L 
            }
        IN TLCEval(RandomElement(Edges))

SPECIFICATION
    Spec

INVARIANT
    TypeOK
    DT1Inv
    InterestingBehavior

PROPERTY
    DT2
    -- CountersConsistent
    -- TreeWithRoot
    -- StableUpEdge

ALIAS
    Alias

CHECK_DEADLOCK
    FALSE

ACTION_CONSTRAINT
    NoSuperfluousIdleSteps
====