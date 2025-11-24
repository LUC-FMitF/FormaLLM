---- MODULE YoYoNoPruning ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS NodeIDs = {0..}  (* All possible node identities *)
CONSTANTS Phases = {"down", "up"}

\* The state of a node in the Yo-Yo algorithm
TypeOK State == <NodeID, Phase, InNeighbors, OutNeighbors, Mailbox>
  NodeID \in NodeIDs
  Phase \in Phases
  InNeighbors \subseteq NodeIDs
  OutNeighbors \subseteq NodeIDs
  Mailbox \subseteq NodeIDs

(* The initial state of a node *)
InitState(NodeID) == <NodeID, "down", {}, {}, {}>

\* Operations on the state of a node
TypeOK Operation == {"send", "receive"}

\* A message sent during the algorithm
TypeOK Message == <Sender, Receiver, Value>
  Sender, Receiver \in NodeIDs
  Value \in NodeIDs

(* The graph of nodes and edges *)
Graph(Nodes) == PartialFunction(NodeIDs, Nodes)

(* A node is a source if it has no incoming neighbors *)
IsSource(State) == EmptySet = State.InNeighbors

(* A node is a sink if it has no outgoing neighbors *)
IsSink(State) == EmptySet = State.OutNeighbors

(* A node is internal if it is both a source and a sink *)
IsInternal(State) == IsSource(State) /\ IsSink(State)

(* The kind of the node: source, sink or internal *)
NodeKind(State) == 
  IF IsSource(State) THEN "source"
  ELSEIF IsSink(State) THEN "sink"
  ELSE "internal"

\* Determine if a message is a down message
IsDownMessage(Msg, State) == Msg.Value \in State.InNeighbors

(* Determine if a message is an up message *)
IsUpMessage(Msg, State) == NOT IsDownMessage(Msg, State)

\* The Yo-Yo algorithm as a state machine
TypeOK NextState(NodeID, Op, Msg, State) == 
  IF Op = "send" THEN
    IF NodeKind(State) = "source" /\ Phase = "down" THEN
      (* A source node in the down phase sends its ID to all outgoing neighbors *)
      <State.NodeID, "up", State.InNeighbors \ State.NodeID, State.OutNeighbors>
    ELSEIF NodeKind(State) = "sink" /\ Phase = "down" THEN
      (* A sink node in the down phase sends its ID to all incoming neighbors *)
      <State.NodeID, "up", State \ State.NodeID, State.InNeighbors>
    ELSEIF NodeKind(State) = "internal" /\ Phase = "down" THEN
      (* An internal node in the down phase sends its ID to all outgoing neighbors *)
      <State.NodeID, "up", State.InNeighbors \ State.NodeID, State.OutNeighbors>
    ELSEIF NodeKind(State) = "source" /\ Phase = "up" THEN
      (* A source node in the up phase sends its ID to all incoming neighbors *)
      <State.NodeID, "down", State \ State.NodeID, State.InNeighbors>
    ELSEIF NodeKind(State) = "sink" /\ Phase = "up" THEN
      (* A sink node in the up phase sends its ID to all outgoing neighbors *)
      <State.NodeID, "down", State.OutNeighbors \ State.NodeID, State.InNeighbors>
    ELSEIF NodeKind(State) = "internal" /\ Phase = "up" THEN
      (* An internal node in the up phase sends its ID to all incoming neighbors *)
      <State.NodeID, "down", State \ State<｜begin▁of▁sentence｜>.NodeID, State.InNeighbors>
    ELSE State
  ELSEIF Op = "receive" THEN
    IF IsDownMessage(Msg, State) THEN
      (* A node receives a down message *)
      <State.NodeID, Phase, State \ State.NodeID, Insert(State.InNeighbors, Msg.Value>
    ELSEIF IsUpMessage(Msg, State) THEN
      (* A node receives an up message *)
      <State.NodeID, Phase, State \ State.NodeID, Delete(State.OutNeighbors, Msg.Value>
    ELSE State
  ELSE State

\* The kind of a node is preserved during the execution of the algorithm *)
TypeOK OKKind == NodeKind(NextState(NodeID, Op, Msg, State)) = NodeKind(State)

(* No new sources are generated during execution of the algorithm *)
TypeOK OKSource == NextState(NodeID, Op, Msg, State).OutNeighbors \ NodeIDs = 0

\* Stabilization condition: there is only one source node, all "down" messages carry 
the identity of that node, all "up" messages say "yes" *)
TypeOK OKStabilize == (NextState(NodeID, Op, Msg, State).InNeighbors = {SourceNode} /\ 
                       All(Msg \in NextState(NodeID, Op, Msg, State).Mailbox, Msg.Value = SourceNode)) /\ 
                      All(Msg \in NextState(NodeID, Op, Msg, State).Mailbox, Msg.Value = "yes")

(* Predicate asserting that there will always be at least two source nodes *)
TypeOK OKSourceCount == Cardinality(NextState(NodeID, Op, Msg, State).InNeighbors) >= 2
====