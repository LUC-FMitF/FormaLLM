---- MODULE MultiPaxos ----
-- TLC configuration for MultiPaxos

-- Model constants
\const Replicas = {1..3}
\const Slots = {1..10}
\const MajorityNum = 2
\const Writes = {...}  -- define the set of write operations
\const NumCommands = {1..10}  -- number of total commands
\const InitState = {...}  -- initial state of the system

-- Formal specification
\extends TLCModelPaxos

-- Invariants
Invariant1 ==> ([] \in State)  -- no stuttering
Invariant2 ==> ([] \in State)  -- no deadlock

-- Procedures
Proc1 ==> ([] \in State)  -- handle prepare
Proc2 ==> ([] \in State)  -- handle prepare replies
Proc3 ==> ([] \in State)  -- handle accept
Proc4 ==> ([] \in State)  -- handle accept replies
Proc5 ==> ([] \in State)  -- handle commit notice

-- Initials
Init == InitState
====