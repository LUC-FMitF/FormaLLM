---- MODULE YoYoNoPruning ----
EXTENDS FiniteSets, Naturals, Sequences

(* The nodes and edges of the graph *)
CONSTANTS Node = {0 ..} (* Identified by integers *)
VARIABLES NeighborsOut, NeighborsIn, Mailbox, Phase :: Node -> {{TRUE}, BOOLEAN}
CHOSEN TYPE MessageType == {DownMessage(value : Nat), UpMessage(value : Nat)}
(* The algorithm orients the edges of the graph. Initially all edges are directed from smaller to larger node identities *)
Initially, FORALL n \in Node -> NeighborsOut[n] = [m | m in Node & (m < n)] /\ Phase[n] = Down(* The phase each node is currently executing *)
(*(*) Mailbox of each node (*) 
Defines operators on finite zero-indexed sequences, where a sequence of length n is represented as a function whose domain is the set {0..(n-1)} (the set {0, 1,..., n-1}). *)
(* The empty zero-indexed sequence *)
EmptyZSeq == <<>> (* The set of valid indices for zero-indexed sequence s *)
ZIndices(s) == IF s = EmptyZSeq THEN {} ELSE DOMAIN s (* The length of zero-indexed sequence s *)
ZLen(s) == IF s = EmptyZSeq THEN 0 ELSE Cardinality(DOMAIN s))(* Lexicographic order on zero-indexed sequences a and b *)
a \preceq b == LET ... IN IsLexLeq(...)(* Rotate the string s to the left by r indices *)
Rotation(s, r) ==  IF s = EmptyZSeq THEN EmptyZSeq ELSE [i in ZIndices(s) |-> s[(i + r) % ZLen(s)]] (* The set of all rotations of zero-indexed sequence s *)
Rotations(s) == ...(* Determine the kind of the node: source, sink or internal. *)
IsSourceNode ==  EXISTS n \in Node : NeighborsOut[n] = {} /\ Phase[n] = Down (* Always true for sinks *)
AlwaysTrueForSink == [](NeighborsIn[n] - {m | m in Node & (Phase[m]=Up)}) \subseteq ...(* Messages sent during the algorithm. *)
SentMessage ==  EXISTS n, m : NeighborsOut[n], Phase[n] = Down ==> Mailbox[m][DownMessage(value)] /\ value <= Min{...} (* Type correctness predicate. *)
YoYoAlgorithmStateMachine == ...(* Formulas used for verification. *)
Formula1 ==  EXISTS n : Node, Phase[n] = Down ==> Mailbox[n][DownMessage(value)] /\ value <= Min{...} (* Predicate asserting that there will always be at least two source nodes. Checking this as an invariant produces an execution that shows that all sources except for the leader will be eliminated *)
Formula2 ==  EXISTS n, m : Node -> ...(* Stabilization condition: there is only one source node, all "down" messages carry the identity of that node, all "up" messages say "yes". *)
NoNewSources == [](NeighborsIn[n] \ {m | (Phase[m] = Down) /\ Mailbox[m][DownMessage(value)]}) \subseteq ...(* No new sources are generated during execution of the algorithm. *)

====