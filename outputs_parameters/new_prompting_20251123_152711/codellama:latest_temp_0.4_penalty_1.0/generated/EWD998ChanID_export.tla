---- MODULE EWD998ChanID_export ----

(**************************************************************************)
(* c properly initialized                                                *)
(* with empty channels.                                                   *)
(**************************************************************************)
CONSTANTS Node = {n1, n2, n3, n4, n5, n6, n7}
VARIABLES Init <- MCInit \* Fewer initial states to speed-up startup.
----------------------------------------------------------------------------
MCInit == 
    /\ c[Node] = [node |-> {}]                   \* Initialize the channels with empty vectors.
    /\ vc[Node] = [node |-> 0]                  \* Initialize the vector clocks to zero for each node.
    /\ state[Node] = [node |-> Idle]            \* Set all nodes to idle initially.
    
Spec ==  
    Init /\ Next \* The next-state relation.

Next ==
    \/ \E t \in Node : MCStep(t)                  \* Each node takes a step in its own behavior.
    \/ \A t \in Node : state[t] = Idle            \* If all nodes are idle, the simulation stops.
    
MCStep(t) ==  
    /\ c'[Node] = [node |-> IF state[node] = Active THEN c[node] U {t} ELSE c[node]]  \* Update the channel with t if node is active.
    /\ vc'[Node] = [node |-> MAX(vc[node], vc[t]) + 1]                                \* Increment the vector clock for all nodes that receive a message from t.
    /\ state'[Node] = [node |-> IF c[node] U {t} != {} THEN Active ELSE Idle]          \* If node receives a message, it becomes active. Otherwise, it stays idle.
    
PostInv == 
    \A t \in Node : vc[t] >= 0                   \* Vector clocks are non-negative integers.
    /\ state[Node] = Idle => c[Node] = {}        \* If a node is idle, its channel should be empty.
    
\* JsonInv *)
JsonInv == TRUE

PostCond == 
    vc[Node] >= 0                           \* Vector clocks are non-negative integers.
    /\ state[Node] = Idle => c[Node] = {}   \* If a node is idle, its channel should be empty.
    
=============================================================================
====