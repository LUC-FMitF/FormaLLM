---- MODULE Majority ----
EXTENDS FiniteSets, Naturals, Sequences, ZSequences

CONSTANTS 
    EmptySequence == <<>>

VARIABLES
    seq \in Seq(Value),
    nextPos \in Nat,
    cand \in Value,
    count \in Nat,
    lowerBound \in Nat

ASSIGN 
    init == seq = <sequence> /\ nextPos = 0 /\ cand = EmptySequence /\ count = 0 /\ lowerBound = 0

DEFINITIONS
    Majority(v) == [i \in ZIndices(seq) |-> seq[i] = v] 

Next == ../MajorityVote/Next.tla

THEOREMS
    Theorem1 == Init /\ []Next
====