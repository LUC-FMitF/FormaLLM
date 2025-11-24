---- MODULE YoYoNoPruning ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS Graph = {(x, y) \in Nat x Nat : x <> y}

\* Definition of nodes and edges
Nodes == DOMAIN Graph
Edges == Graph
SourceNode(n) == EXISTS m \in Edges [HEAD(m) = n]
SinkNode(n)   == EXISTS m \in Edges [TAIL(m) = n]
InternalNode(n) == !SourceNode(n) /\ !SinkNode(n)
NeighborOf(n, m) == (HEAD(m) = n) \/ (TAIL(m) = n)
EdgeBetween(n, m) == EXISTS e \in Edges [HEAD(e) = n /\ TAIL(e) = m]
DownMessage(n, m) == EXISTS msg \in Messages [HEAD(msg) = n /\ TAIL(msg) = m /\ BODY(msg) <> n]
UpMessage(n, m)   == EXISTS msg \in Messages [HEAD(msg) = m /\ TAIL(msg) = n /\ BODY(msg) = n]

\* Definition of the phase
Phase == {Down, Up}
NodeStatus(n) == IF SourceNode(n) THEN Down ELSE IF SinkNode(n) THEN Up ELSE Idle

\* Definition of mailboxes
Mailbox(n) == [i \in Naturals |-> (HEAD(i), TAIL(i))] : i \in Messages /\ BODY(i) = n

\* Definition of messages
Messages == UNION {[0, 1, n] : n \in Nodes}
MessageBody(msg) == IF HEAD(msg) < TAIL(msg) THEN HEAD(msg) ELSE TAIL(msg)

\* Specification of the down phase
DownPhase == [n \in Nodes |-> DownNode(n)] : DownNode(n) == EXISTS m \in Mailbox(n) [MessageBody(m) < n]

\* Specification of the up phase
UpPhase == [n \in Nodes |-> UpNode(n)] : UpNode(n) == EXISTS m \in Mailbox(n) [MessageBody(m) = n]

\* Invariants for correctness checking
Invariant1 == ![n \in Nodes |-> SourceNode(n)] SUBSET DownPhase
Invariant2 == ![n \in Nodes |-> SinkNode(n)] SUBSET UpPhase
Invariant3 == [n \in Nodes |-> IF NodeStatus(n) = Down THEN EXISTS m \in Mailbox(n) [MessageBody(m) < n] ELSE TRUE]
Invariant4 == [n \in Nodes |-> IF NodeStatus(n) = Up THEN EXISTS m \in Mailbox(n) [MessageBody(m) = n] ELSE TRUE]

\* State machine representation of the algorithm
State == {DownPhase, UpPhase}
NextState(s) == IF s = DownPhase THEN UpPhase ELSE DownPhase

\* Formulas used for verification
Formula1 == [n \in Nodes |-> EXISTS m \in Mailbox(n) [MessageBody(m) < n]] SUBSET DownPhase
Formula2 == [n \in Nodes |-> IF NodeStatus(n) = Up THEN EXISTS m \in Mailbox(n) [MessageBody(m) > n] ELSE TRUE] SUBSET UpPhase

\* Additional invariants and assertions
Assertion1 == ![n \in Nodes : SourceNode(n)] > 1
====