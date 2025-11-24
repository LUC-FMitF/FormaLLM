---- MODULE EWD998ChanID_export ----

(******************************************************************************)
(* This is a simple model of vector clocks in distributed systems. Each node   *)
(* maintains a local vector clock, which increments every time it receives     *)
(* messages from other nodes.                                                *)
(******************************************************************************)

CONSTANTS Node = {n1, n2, n3}  (* The set of all nodes in the system. *)
VARIABLES Clock[Node]           (* A vector clock for each node. *)

Init == \* Initialize state with an initial condition where every node's clock is at time zero.
    /\ [n \in Node |-> (Clock[n] = 0)] 
    
Next == ~([]Node - {x} U []Node) * Clock' = IF x \in Domain(Clock') THEN Clock' ELSE Clock + 1 ENDIF   (* Each node increments its clock at each step. *)

Spec == Init /\ [][Next]_<<Clock>>  (* The initial state and the transition relation are combined into a specification. *)
    
PostInv == ~([]Node - {x} U []Node) * Clock' = IF x \in Domain(Clock') THEN Clock' ELSE MAX{Clock[y] : y \in Node, y != x } + 1 ENDIF  (* A post-invariant that ensures each node's clock is at least the maximum of all other nodes. *)
    
THEOREM Spec => []PostInv   (* The specification implies the post invariant. *)
===============================================================================
====
TLC Configuration:
CONSTANTS Node = {n1, n2, n3}  Init <- MCInit /\ [][Next]_<<Clock>>
SPECIFICATION Spec
INVARIANT PostInv
CHECK_DEADLOCK FALSE
====