---- MODULE YoYoNoPruning ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS
  Source = "source"
  Internal = "internal"
  Sink = "sink"
  
  Down = "down"
  Up = "up"
  
  Yes = "yes"
  No = "no"
  
  NodeId = 0..Infinity - {n : Node in Nodes} -- nodes are identified by integers
  Edge = {Subset(POWERSET(NodeId), 2)} -- edges of the graph
  
  InitialPhase = Down /\ Up -- initial phase of each node
  Phases = {{Down}, {Up}} -- set of phases
  
  Nodes = NodeId \ X -- nodes in the system
  Neighbor[n] = {m : m != n, (m, n) IN Edge} -- neighbors of a node
  IncomingNeighbor[n][m] = (m, n) IN Edge /\ m != n -- incoming neighbor of a node
  
  Msg = NodeId \ X -- messages sent during the algorithm
  DownMsg[n] = {m : (m, n) IN Edge /\ m < n} -- down messages from neighbors to a node
  UpMsg[n] = {m : (n, m) IN Edge /\ m > n} -- up messages from neighbors to a node
  
  NodeType[n] == IF Cardinality(DownMsg[n]) > 1 \/ NodeKind[n] = Source THEN Source ELSE Internal
  NodeKind[n] == IF DownMsg[n] = {} /\ UpMsg[n] != {} THEN Sink ELSE NodeType[n]
  
  NodeState[n][p] = -- state of a node in a phase
    CASE p OF {Down} -> MIN(DownMsg[n]) UNION {n} IF DownMsg[n] != {} ELSE {};
    [p] -> MAX(UpMsg[n]) UNION {n} IF UpMsg[n] != {} ELSE {}
  
  NodeStates = -- states of all nodes in a phase
    {n : n \in Nodes /\ p \in Phases |-> NodeState[n][p]}
  
  SourceNodes = {n : n \in Nodes /\ NodeKind[n] = Source} -- source nodes
  InternalNodes = {n : n \in Nodes /\ NodeKind[n] = Internal} -- internal nodes
  SinkNodes = {n : n \in Nodes /\ NodeKind[n] = Sink} -- sink nodes
  
  MsgSentDuringAlgorithm == UNION({m : m \in DownMsg[n], n \in SourceNodes})
                          UNION({m : m \in UpMsg[n], n \in SinkNodes})
                          
SPECIFICATION Spec /\ INVARIANTS Inv_AtLeast2SourceNodes

Inv_AtLeast2SourceNodes == EXISTS(s1, s2 : s1 != s2 /\ s1 \in SourceNodes /\ s2 \in SourceNodes)

OPERATIONS
  Init == <>

  Next[n] == -- next state of a node n in the algorithm
    IF NodeKind[n] = Source THEN
      IF NodeState[n][Down] != {} THEN NodeState[n][Up] ELSE NodeState[n][Down]
    ELSE
      IF NodeState[n][Down] = {MAX(NodeStates[x], Down) : x \in Nodes} THEN NodeState[n][Down]
      ELSEIF NodeState[n][Down] != {} THEN NodeState[n][Up]
      ELSE NodeState[n][Down]
    ENDIF;
  
  NextStates == -- next states of all nodes in the algorithm
    [n : n \in Nodes |-> Next[n]]
    
OPERATIONALIZES
  Init -> <NodeKind = Source /\ NodeState[n][Down] = {n} FORALL n \in Nodes, NodeState[n][Up] = {} FORALL n \in SinkNodes>
  [next states] -> <NextStates>
  
END MODULE Yoyo ----
====