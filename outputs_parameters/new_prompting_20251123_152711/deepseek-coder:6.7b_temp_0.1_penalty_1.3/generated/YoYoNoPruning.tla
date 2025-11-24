---- MODULE YoYoNoPruning ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS
  Source, Sink, Internal = {Source, Sink, Internal}
  Down, Up = {Down, Up}
  No, Yes = {No, Yes}
  MinValue = MinValue

ASSUME
  \* The nodes are represented by their integer identities
  NodeIDs = {NodeID : NodeID \in Nat}

  \* The phase each node is currently executing
  Phases = NodeID \in NodeIDs -> {Down, Up}

  \* Incoming and outgoing neighbors of each node
  Neighbors = NodeID \in NodeIDs -> Powerset(NodeIDs)

  \* Mailbox of each node
  Mailboxes = NodeID \in NodeIDs -> Sequences(NodeIDs)

  \* Kind of the node: source, sink or internal
  NodeKind = NodeID \in NodeIDs -> {Source, Sink, Internal}

  \* Messages sent during the algorithm
  Messages = NodeID \in NodeIDs -> NodeID \in NodeIDs -> {No, Yes}

  \* Type correctness predicate
  TypeOK =
    \* Each node has at least one incoming neighbor
    EVERY NodeID \in NodeIDs -> EXISTS n \in NodeIDs : NodeID \in Neighbors[n]
    \* Each node has at least one outgoing neighbor
    EVERY NodeID \in NodeIDs -> EXISTS n \in NodeIDs : NodeID \in Neighbors[n]
    \* Each node has at least one message
    EVERY NodeID \in NodeIDs -> EXISTS n \in NodeIDs : NodeID \in Domain(Mailboxes[n])

  \* Yo-Yo algorithm as a state machine
  StateMachine =
    \* Initial state
    INIT == [NodeID \in NodeIDs |-> (Neighbors[NodeID], Mailboxes[NodeID], Phases[NodeID])]
    \* Transition function
    NEXT(state) ==
      [NodeID \in NodeIDs |-> (Neighbors[NodeID], Mailboxes[NodeID], Phases[NodeID])]

  \* Down phase: we distinguish sources and other nodes
  DownPhase =
    \* Source nodes broadcast their identity to all neighbors
    SourceNodes == [NodeID \in NodeIDs |-> NodeKind[NodeID] = Source]
    \* Other nodes wait for values to have been received from all incoming neighbors, then broadcast the minimum value that has been received to all outgoing neighbors
    OtherNodes == [NodeID \in NodeIDs |-> NodeKind[NodeID] \in {Sink, Internal}]

  \* Up phase, again distinguishing sources and other nodes
  UpPhase =
    \* Source nodes reply "yes" to all neighbors that sent the minimum value
    SourceNodes == [NodeID \in NodeIDs |-> NodeKind[NodeID] = Source]
    \* Other nodes wait until messages for the up phase have been received from all outgoing neighbors
    OtherNodes == [NodeID \in NodeIDs |-> NodeKind[NodeID] \in {Sink, Internal}]

  \* Formulas used for verification
  Formulas =
    \* Predicate asserting that there will always be at least two source nodes
    AtLeastTwoSources == EXISTS a, b \in NodeIDs : NodeKind[a] = Source /\ NodeKind[b] = Source /\ a \neq b

  \* Stabilization condition: there is only one source node, all "down" messages carry the identity of that node, all "up" messages say "yes"
  Stabilization =
    \* There is only one source node
    OnlyOneSource == EXISTS a \in NodeIDs : NodeKind[a] = Source /\ EVERY b \in NodeIDs : NodeKind[b] \neq Source
    \* All "down" messages carry the identity of that node
    DownMessages == EVERY NodeID \in NodeIDs : EXISTS n \in Domain(Mailboxes[NodeID]) : Messages[NodeID][n] = NodeID
    \* All "up" messages say "yes"
    UpMessages == EVERY NodeID \in NodeIDs : EXISTS n \in Domain(Mailboxes[NodeID]) : Messages[NodeID][n] = Yes

INVARIANTS
  \* No new sources are generated during execution of the algorithm
  NoNewSources == EVERY NodeID \in NodeIDs : NodeKind[NodeID] \neq Source
  \* Node m is an outgoing neighbor of node n iff n is an incoming neighbor of m, except if the edge is being reversed, in which case there is a "no" message in one of the mailboxes
  OutgoingNeighbors == EVERY NodeID \in NodeIDs : EVERY m \in Neighbors[NodeID] : m \in Neighbors[NodeID]

SPECIFICATION
  \* The specification of the Yo-Yo leader election algorithm
  Spec == EVERY NodeID \in NodeIDs : EXISTS n \in NodeIDs : NodeID \in Neighbors[n]

TLC Configuration:
  CONSTANTS
    Model = YoYo
  SPECIFICATION
    Spec
  INVARIANTS
    TypeOK
    StateMachine
    DownPhase
    UpPhase
    Formulas
    Stabilization
    NoNewSources
    OutgoingNeighbors
====