---- MODULE YoYoNoPruning ----
EXTENDS FiniteSets, Naturals, Sequences

(* CONSTANTS *)
CONSTANT Node = {0 .. 2^31 - 1} (* Set of node identities *)

(* Type OK for type invariants *)
TypeOK == [NODE]SUBSET Node

(* Definitions *)
SOURCE  == {n \in Node |-> NONE}
SINK    == {n \in Node |-> NONE}
INTERNAL == {n \in Node |-> NONE}
DIRECTION == {n \in Node |-> TT} (* True means outgoing, False means incoming *)
NEIGHBORS(node) == 
  [i \in ZIndices(SOURCE[NODE]) -> 
     IF SOURCE[NODE][i] = node THEN 0 ELSE SOURCE[NODE][i] ENDIF] UNION 
  [i \in ZIndices(SINK[NODE]) -> 
     IF SINK[NODE][i] = node THEN <｜begin▁of▁sentence｜> ELSE SINK[NODE][i] ENDIF]

(* Initialize nodes *)
INIT == <<>> IN Node /\ NODE = {0}

(* Define state variables for each node's phase and incoming/outgoing neighbors *)
PHASE  == {n \in Node |-> BOOLEAN} (* True means down, False means up *)
MSG    == {n \in Node |-> 2^Node} 
IN_NEIGHBOR(node) == 
  [i \in ZIndices(SOURCE[NODE]) -> SOURCE[NODE][i]] UNION 
  [i \in ZIndices(SINK[NODE]) -> SINK[NODE][i]]
OUT_NEIGHBOR(node) == 
  IF PHASE[node] THEN NEIGHBORS(node) ELSE {}

(* Determine the kind of a node *)
IS_SOURCE == [n \in Node |-> 0 < #{i \in ZIndices(IN_NEIGHBOR(n)) : n IN IN_NEIGHBOR(i)}]
IS_SINK    == [n \in Node |-> #{i \in ZIndices(OUT_NEIGHBOR(n)) : n IN OUT_NEIGHBOR(i)} = 0]
IS_INTERNAL == {n \in Node - IS_SOURCE - IS_SINK}

(* Define the mailbox of a node *)
MAILBOX(node) == 
  [m \in ZIndices(MSG[node]) |-> (MSG[node][m], DIRECTION[MSG[node][m]]) IN MSG[NODE] /\ m > 0]

(* Predicate asserting that there will always be at least two source nodes *)
AtLeastTwoSources == #{n \in Node : IS_SOURCE[n]} >= 2

(* Down phase: we distinguish sources and other nodes. *)
DownPhase(node) == 
  IF DIRECTION[node] THEN (* node is outgoing *)
    [m \in ZIndices(IN_NEIGHBOR(node)) |-> MSG[NODE][MSG[node][m]] := MINIMUM(MSG[NODE][m], MSG[NODE][node])] 
  ELSE (* node is incoming *)
    [n \in ZIndices(OUT_NEIGHBOR(node)) |-> IF OUT_NEIGHBOR[node][n] < MSG[node][node] THEN DIRECTION[OUT_NEIGHBOR[node][n]] := FALSE FI] 

(* Up phase: again distinguishing sources and other nodes. *)
UpPhase(node) == 
  IF ~DIRECTION[node] THEN (* node is incoming *)
    [m \in ZIndits(IN_NEIGHBOR(node)) |-> MSG[NODE][MSG[node][m]] := MAXIMUM(MSG[NODE][m], MSG[NODE][node]) /\ DIRECTION[OUT_NEIGHBOR[node][n]] := TRUE] 
  ELSE (* node is outgoing *)
    [n \in ZIndits(OUT_NEIGHBOR(node)) |-> IF OUT_NEIGHBOR[node][n] = MSG[NODE][0] THEN DIRECTION[OUT_NEIGHBOR[node][n]] := FALSE FI /\ IF OUT_NEIGHBOR[node][n] > MSG[NODE][0] THEN DIRECTION[OUT_NEIGHBOR[node][n]] := TRUE FI] 

(* Node m is an outgoing neighbor of node n iff n is an incoming neighbor of m, except if the edge is being reversed *)
NodeRelation == [m \in ZIndices(OUT_NEIGHBOR(n)) |-> (MSG[NODE][m], DIRECTION[MSG[NODE][m]]) IN MSG[NODE]] UNION 
                [n \in ZIndices(IN_NEIGHBOR(m)) -> 
                  IF IN_NEIGHBOR[m][n] = node THEN (node, ~DIRECTION[node]) IN MSG[NODE] ELSE (IN_NEIGHBOR[m][n], DIRECTION[IN_NEIGHBOR[m][n]]) IN MSG[NODE] FI]

(* Stabilization condition: there is only one source node, all "down" messages carry the identity of that node, and all "up" messages say "yes". *)
StabilityCondition == #{n \in Node : IS_SOURCE[n]} = 1 /\ [m \in ZIndices(MSG[NODE]) |-> MSG[NODE][m] = NODE[0]] 

(* Formulas used for verification *)
FormulaeForVerification == DownPhaseVerify /\ UpPhaseVerify
DownPhaseVerify == 
  [n \in ZIndices(IS_SOURCE) |-> DownPhase(IS_SOURCE[n])] IMPLIES (#{i \in ZIndits(MSG[NODE][i]) : MSG[NODE][i] < NODE[0]} = 1)
UpPhaseVerify == 
  [n \in ZIndices(IS_SINK) |-> UpPhase(IS_SINK[n])] IMPLIES (#{i \in ZIndits(MSG[NODE][i]) : MSG[NODE][i] > NODE[0]} = 1 /\ #{i \in ZIndices(DIRECTION) : DIRECTION[i] = TRUE} >= 2)

(* Correctness predicate *)
CorrectnessPredicate == NodeRelation /\ StabilityCondition /\ AtLeastTwoSources 

(* Yo-Yo algorithm as a state machine *)
StateMachine == 
  [n \in ZIndices(Node) |-> 
    IF IS_SOURCE[NODE[n]] THEN DownPhase(NODE[n]) ELSE UpPhase(NODE[n]) FI]
IMPLEMENTS CorrectnessPredicate /\ FormulaeForVerification
====