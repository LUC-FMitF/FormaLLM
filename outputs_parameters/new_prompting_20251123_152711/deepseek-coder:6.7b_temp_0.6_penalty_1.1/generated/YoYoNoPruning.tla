---- MODULE YoYoNoPruning ----
EXTENDS FiniteSets, Naturals, Sequences

(* Define types *)
TYPE Node == {n: \in Nat}
TYPE Message == {val: \in Nat, from: Node}
TYPE Edge == [fromNode: Node, toNode: Node] * (fromNode < toNode)
TYPE Graph == {nodes: SetOf[Node], edges: SetOf[Edge]}

(* Define constants *)
CONSTANTS Nodes == {n \in Nat : n > 0}  (* The set of nodes in the graph *)

(* Define variables *)
VARIABLES Phase, Leader, NeighborsIn, NeighborsOut, Mailbox == [Node -> Message]

(* Define operators on finite zero-indexed sequences *)
OPERATOR MsgFromZSeq(s) == IF s = EmptyZSeq THEN {} ELSE {[i \in ZIndices(s) |-> (VAL(ELT(s, i)))] : i \in ZIndices(s)} END
OPERATOR MinMsg(m1, m2) == IF m1.val < m2.val THEN m1 ELSE m2

(* Define invariants *)
INVARIANT IsSourceNode(n) == EXISTS {i : Node} [i \in NeighborsIn[n]] /\ (NeighborsOut[n] = {})
INVARIANT IsSinkNode(n) == EXISTS {i : Node} [i \in NeighborsOut[n]] /\ (NeighborsIn[n] = {})
INVARIANT IsInternalNode(n) == NOT IsSourceNode(n) /\ NOT IsSinkNode(n)

(* Define the Yo-Yo algorithm as a state machine *)
STATE Init == \state InitState()
TRANSITION Any - "down" -> DownPhase
TRANSITION DownPhase & Leader = n /\ Phase = "up" - "up" -> UpPhase
TRANSITION DownPhase & Leader = n /\ Phase = "up" - Init -> InitState()

(* Define the transition functions *)
FUNCTION InitState == BEGIN
  (* Initialize variables *)
  NeighborsIn := [n \in Nodes |-> 0]
  NeighborsOut := [n \in Nodes |-> 0]
  Mailbox := [n \in Nodes |-> {val: 0, from: n}]
  Phase := "down"
END
FUNCTION DownPhase == BEGIN
  (* Check if it's a source node *)
  IF IsSourceNode(Leader) THEN
    Mailbox[NextNeighbor] := MinMsg(Mailbox[NextNeighbor], {val: Leader, from: Current})
  ENDIF
  Phase := "up"
END
FUNCTION UpPhase == BEGIN
  (* Check if it's a source node *)
  IF IsSourceNode(Leader) THEN
    Mailbox[NextNeighbor] := {val: Leader, from: Current}
  ELSE
    Mailbox[Current] := {val: MIN {m.val : m \in MsgFromZSeq(Mailbox[Current])}, from: EXTREME ({n : n \in Nodes : NeighborsIn[n]} INTERSECT {n : n \in Nodes : Mailbox[n] \neq {} })}
  ENDIF
  Phase := "down"
END

(* Define the kind of a node *)
FUNCTION Kind(n) == IF IsSourceNode(n) THEN "source" ELSEIF IsSinkNode(n) THEN "sink" ELSE "internal"

====
-- TLC Configuration --
CONSTANTS N = 5 (* Number of nodes in the graph *)
(* Add more configuration here *)
=============================================================================