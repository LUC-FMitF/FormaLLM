----------------------- MODULE CheckpointCoordination -----------------------
EXTENDS
Naturals,
FiniteSets,
Sequences

CONSTANTS
Node,
Majority

VARIABLES
IsNodeUp,
NetworkPath,
Leader,
ReplicatedLog,
ExecutionCounter,
LastVotePayload,
CurrentLease,
CanTakeCheckpoint,
IsTakingCheckpoint,
TimeoutCounter,
LatestCheckpoint

EnvironmentVars == <<
IsNodeUp,
NetworkPath
>>

PaxosVars == <<
Leader,
ReplicatedLog,
ExecutionCounter,
LastVotePayload
>>

CheckpointVars == <<
CurrentLease,
CanTakeCheckpoint,
IsTakingCheckpoint,
TimeoutCounter,
LatestCheckpoint
>>

AllVars == <<
IsNodeUp,
NetworkPath,
Leader,
ReplicatedLog,
ExecutionCounter,
LastVotePayload,
CurrentLease,
CanTakeCheckpoint,
IsTakingCheckpoint,
TimeoutCounter,
LatestCheckpoint
>>

NoNode == CHOOSE n : n \notin Node

Log == Seq(Node \cup {NoNode})

LogIndex == Nat \ {0}

MinLogIndex == 1

BlankLog == [i \in LogIndex |-> NoNode]

LogCheckpoint == [
log     : Log,
counter : LogIndex
]

CheckpointLease == [
node    : Node,
counter : LogIndex
]

NoCheckpointLease == CHOOSE lease : lease \notin CheckpointLease

ReadLog(node, index) ==
IF index \in DOMAIN ReplicatedLog[node]
THEN ReplicatedLog[node][index]
ELSE NoNode

WriteLog(node, index, value) == [
[i \in LogIndex |-> ReadLog(node, i)] EXCEPT ![index] = value
]

MergeLogs(srcNode, dstNode) == [
i \in LogIndex |->
IF ReadLog(dstNode, i) /= NoNode
THEN ReadLog(dstNode, i)
ELSE ReadLog(srcNode, i)
]

OpenIndices == {
i \in LogIndex :
\A n \in Node :
ReadLog(n, i) = NoNode
}

FirstOpenIndex ==
CHOOSE index \in OpenIndices :
\A other \in OpenIndices :
index <= other

TypeInvariant ==
/\ IsNodeUp \in [Node -> BOOLEAN]
/\ NetworkPath \in [Node \X Node -> BOOLEAN]
/\ Leader \in Node \cup {NoNode}
/\ ReplicatedLog \in [Node -> Log]
/\ ExecutionCounter \in [Node -> LogIndex]
/\ LastVotePayload \in [Node -> LogIndex]
/\ CurrentLease \in [Node -> (CheckpointLease \cup {NoCheckpointLease})]
/\ CanTakeCheckpoint \in [Node -> BOOLEAN]
/\ IsTakingCheckpoint \in [Node -> BOOLEAN]
/\ TimeoutCounter \in LogIndex
/\ LatestCheckpoint \in LogCheckpoint

SafetyInvariant ==
/\ Leader /= NoNode =>

/\ ~CanTakeCheckpoint[Leader]
/\ ~IsTakingCheckpoint[Leader]

/\ CurrentLease[Leader] = NoCheckpointLease =>
/\ \A n \in Node :
/\ ~CanTakeCheckpoint[n]
/\ ~IsTakingCheckpoint[n]

/\ CurrentLease[Leader] /= NoCheckpointLease =>
/\ \A n \in Node :
/\ (CanTakeCheckpoint[n] \/ IsTakingCheckpoint[n]) =>
/\ CurrentLease[Leader].node = n

/\ \A n1, n2 \in Node :
/\ (CanTakeCheckpoint[n1] /\ CanTakeCheckpoint[n2]) =>
/\ n1 = n2
/\ (IsTakingCheckpoint[n1] /\ IsTakingCheckpoint[n2]) =>
/\ n1 = n2

/\ \A n \in Node :
/\ IsTakingCheckpoint[n] => CanTakeCheckpoint[n]
/\ CanTakeCheckpoint[n] => (CurrentLease[n] /= NoCheckpointLease)
/\ CanTakeCheckpoint[n] => CurrentLease[n].node = n
/\ CanTakeCheckpoint[n] => CurrentLease[n].counter >= TimeoutCounter

/\ \A i \in LogIndex :
/\ \A n1, n2 \in Node :
\/ ReadLog(n1, i) = NoNode
\/ ReadLog(n2, i) = NoNode
\/ ReadLog(n1, i) = ReadLog(n2, i)

TemporalInvariant ==

/\ <>(\E n \in Node : CanTakeCheckpoint[n])

/\ \A n \in Node :
/\ CanTakeCheckpoint[n] ~>
\/ IsTakingCheckpoint[n]
\/ ~IsNodeUp[n]
\/ CurrentLease[n].counter < TimeoutCounter

/\ \A n \in Node :
/\ IsTakingCheckpoint[n] ~>
\/ LastVotePayload[n] = ExecutionCounter[n]
\/ ~IsNodeUp[n]
\/ CurrentLease[n].counter < TimeoutCounter

/\ <>(LatestCheckpoint /= BlankLog)

ConnectedOneWay(src, dst) ==
/\ IsNodeUp[src]
/\ IsNodeUp[dst]
/\ NetworkPath[src, dst]

Connected(src, dst) ==
/\ ConnectedOneWay(src, dst)
/\ ConnectedOneWay(dst, src)

HaveQuorumFrom[leader \in Node] ==
LET available == {n \in Node : Connected(leader, n)} IN
/\ IsNodeUp[leader]
/\ Cardinality(available) >= Majority

HaveQuorum ==
/\ Leader /= NoNode
/\ HaveQuorumFrom[Leader]

NodeFailure(n) ==
/\ IsNodeUp' = [IsNodeUp EXCEPT ![n] = FALSE]
/\ Leader' = IF n = Leader THEN NoNode ELSE Leader
/\ ExecutionCounter' = [ExecutionCounter EXCEPT ![n] = MinLogIndex]
/\ LastVotePayload' = [LastVotePayload EXCEPT ![n] = MinLogIndex]
/\ CurrentLease' = [CurrentLease EXCEPT ![n] = NoCheckpointLease]
/\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = FALSE]
/\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
/\ UNCHANGED <<NetworkPath>>
/\ UNCHANGED <<ReplicatedLog>>
/\ UNCHANGED <<TimeoutCounter, LatestCheckpoint>>

NodeRecovery(n) ==
/\ ~IsNodeUp[n]
/\ IsNodeUp' = [IsNodeUp EXCEPT ![n] = TRUE]
/\ ReplicatedLog' =
[ReplicatedLog EXCEPT ![n] =
SubSeq(LatestCheckpoint.log, MinLogIndex, LatestCheckpoint.counter - 1)
\o SubSeq(@, LatestCheckpoint.counter, Len(@))]
/\ ExecutionCounter' = [ExecutionCounter EXCEPT ![n] = LatestCheckpoint.counter]
/\ LastVotePayload' = [LastVotePayload EXCEPT ![n] = MinLogIndex]
/\ CurrentLease' = [CurrentLease EXCEPT ![n] = NoCheckpointLease]
/\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = FALSE]
/\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
/\ UNCHANGED <<NetworkPath>>
/\ UNCHANGED <<Leader>>
/\ UNCHANGED <<TimeoutCounter, LatestCheckpoint>>

NetworkFailure(src, dst) ==
/\ src /= dst
/\ NetworkPath' = [NetworkPath EXCEPT ![src, dst] = FALSE]
/\ UNCHANGED <<IsNodeUp>>
/\ UNCHANGED PaxosVars
/\ UNCHANGED CheckpointVars

NetworkRecovery(src, dst) ==
/\ NetworkPath' = [NetworkPath EXCEPT ![src, dst] = TRUE]
/\ UNCHANGED <<IsNodeUp>>
/\ UNCHANGED PaxosVars
/\ UNCHANGED CheckpointVars

ElectLeader(n) ==
/\ Leader = NoNode
/\ IsNodeUp[n]
/\ ~IsTakingCheckpoint[n]
/\ HaveQuorumFrom[n]
/\ ExecutionCounter[n] = FirstOpenIndex
/\ Leader' = n
/\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = FALSE]
/\ UNCHANGED EnvironmentVars
/\ UNCHANGED <<ReplicatedLog, ExecutionCounter, LastVotePayload>>
/\ UNCHANGED <<CurrentLease, IsTakingCheckpoint, TimeoutCounter, LatestCheckpoint>>

ShouldReplaceLease(currentLease) ==

\/ currentLease.counter < TimeoutCounter

\/  /\ Connected(Leader, currentLease.node)
/\ currentLease.counter < LastVotePayload[currentLease.node]

SendReplicatedRequest(prospect) ==
LET currentLease == CurrentLease[Leader] IN
LET index == FirstOpenIndex IN
/\ HaveQuorum
/\ Leader /= prospect
/\ Connected(Leader, prospect)
/\ currentLease /= NoCheckpointLease => ShouldReplaceLease(currentLease)
/\ ReplicatedLog' =
[n \in Node |->
IF ConnectedOneWay(Leader, n)
THEN WriteLog(n, index, prospect)
ELSE ReplicatedLog[n]]
/\ CurrentLease' = [
CurrentLease EXCEPT ![Leader] = [
node    |-> prospect,
counter |-> index
]
]
/\ UNCHANGED EnvironmentVars
/\ UNCHANGED <<Leader, ExecutionCounter, LastVotePayload>>
/\ UNCHANGED <<CanTakeCheckpoint, IsTakingCheckpoint, TimeoutCounter, LatestCheckpoint>>

PropagateReplicatedRequest(src, dst) ==
/\ ConnectedOneWay(src, dst)
/\ ReplicatedLog' = [ReplicatedLog EXCEPT ![dst] = MergeLogs(src, dst)]
/\ UNCHANGED EnvironmentVars
/\ UNCHANGED <<Leader, ExecutionCounter, LastVotePayload>>
/\ UNCHANGED CheckpointVars

ProcessReplicatedRequest(n) ==
LET request == ReadLog(n, ExecutionCounter[n]) IN
LET isTimedOut == ExecutionCounter[n] < TimeoutCounter IN
/\ IsNodeUp[n]
/\ ~IsTakingCheckpoint[n]
/\ request /= NoNode
/\ CanTakeCheckpoint' = [
CanTakeCheckpoint EXCEPT ![n] =
/\ Leader /= n
/\ n = request
/\ ~isTimedOut
]
/\ CurrentLease' =
IF n = Leader
THEN CurrentLease
ELSE [
CurrentLease EXCEPT ![n] =
IF isTimedOut
THEN NoCheckpointLease
ELSE [node |-> request, counter |-> ExecutionCounter[n]]
]
/\ ExecutionCounter' = [ExecutionCounter EXCEPT ![n] = @ + 1]
/\ UNCHANGED EnvironmentVars
/\ UNCHANGED <<Leader, ReplicatedLog, LastVotePayload>>
/\ UNCHANGED <<IsTakingCheckpoint, TimeoutCounter, LatestCheckpoint>>

StartCheckpoint(n) ==
/\ CanTakeCheckpoint[n]
/\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = TRUE]
/\ UNCHANGED EnvironmentVars
/\ UNCHANGED PaxosVars
/\ UNCHANGED <<CurrentLease, CanTakeCheckpoint, TimeoutCounter, LatestCheckpoint>>

FinishCheckpoint(n) ==
/\ IsTakingCheckpoint[n]
/\ LastVotePayload' = [LastVotePayload EXCEPT ![n] = ExecutionCounter[n]]
/\ CurrentLease' = [CurrentLease EXCEPT ![n] = NoCheckpointLease]
/\ CanTakeCheckpoint' = [CanTakeCheckpoint EXCEPT ![n] = FALSE]
/\ IsTakingCheckpoint' = [IsTakingCheckpoint EXCEPT ![n] = FALSE]
/\ LatestCheckpoint' = [
log     |-> SubSeq(
ReplicatedLog[n],
MinLogIndex,
ExecutionCounter[n] - 1
),
counter |-> ExecutionCounter[n]
]
/\ UNCHANGED EnvironmentVars
/\ UNCHANGED <<Leader, ReplicatedLog, ExecutionCounter>>
/\ UNCHANGED <<TimeoutCounter>>

TriggerTimeout ==
/\ \E n \in Node : ReadLog(n, TimeoutCounter) /= NoNode
/\ TimeoutCounter' = TimeoutCounter + 1
/\ CanTakeCheckpoint' = [
n \in Node |->
/\ CanTakeCheckpoint[n]
/\ CurrentLease[n].counter > TimeoutCounter
]
/\ IsTakingCheckpoint' = [
n \in Node |->
/\ IsTakingCheckpoint[n]
/\ CurrentLease[n].counter > TimeoutCounter
]
/\ UNCHANGED EnvironmentVars
/\ UNCHANGED PaxosVars
/\ UNCHANGED <<CurrentLease, LatestCheckpoint>>

Init ==
/\ IsNodeUp = [n \in Node |-> TRUE]
/\ NetworkPath = [src, dst \in Node |-> TRUE]
/\ Leader = NoNode
/\ ReplicatedLog = [n \in Node |-> BlankLog]
/\ ExecutionCounter = [n \in Node |-> MinLogIndex]
/\ LastVotePayload = [n \in Node |-> MinLogIndex]
/\ CurrentLease = [n \in Node |-> NoCheckpointLease]
/\ CanTakeCheckpoint = [n \in Node |-> FALSE]
/\ IsTakingCheckpoint = [n \in Node |-> FALSE]
/\ TimeoutCounter = MinLogIndex
/\ LatestCheckpoint = [log |-> BlankLog, counter |-> MinLogIndex]

Next ==
\/ \E n \in Node : NodeFailure(n)
\/ \E n \in Node : NodeRecovery(n)
\/ \E src, dst \in Node : NetworkFailure(src, dst)
\/ \E src, dst \in Node : NetworkRecovery(src, dst)
\/ \E n \in Node : ElectLeader(n)
\/ \E n \in Node : SendReplicatedRequest(n)
\/ \E src, dst \in Node : PropagateReplicatedRequest(src, dst)
\/ \E n \in Node : ProcessReplicatedRequest(n)
\/ \E n \in Node : StartCheckpoint(n)
\/ \E n \in Node : FinishCheckpoint(n)
\/ TriggerTimeout

TemporalAssumptions ==
/\ \A n \in Node : WF_AllVars(NodeRecovery(n))
/\ \A src, dst \in Node : WF_AllVars(NetworkRecovery(src, dst))
/\ \A n \in Node : SF_AllVars(ElectLeader(n))
/\ \A n \in Node : SF_AllVars(SendReplicatedRequest(n))
/\ \A src, dst \in Node : SF_AllVars(PropagateReplicatedRequest(src, dst))
/\ \A n \in Node : SF_AllVars(ProcessReplicatedRequest(n))
/\ \A n \in Node : SF_AllVars(StartCheckpoint(n))
/\ \A n \in Node : SF_AllVars(FinishCheckpoint(n))

Spec ==
/\ Init
/\ [][Next]_AllVars
/\ TemporalAssumptions

THEOREM Spec =>
/\ []TypeInvariant
/\ []SafetyInvariant
/\ []TemporalInvariant

=============================================================================
