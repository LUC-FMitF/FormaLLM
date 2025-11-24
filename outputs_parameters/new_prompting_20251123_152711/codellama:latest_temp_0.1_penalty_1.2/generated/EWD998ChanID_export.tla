---- MODULE EWD998ChanID_export ----

(***************************************************************************)
(* c properly initialized                                                 *)
(* with empty channels.                                                     *)
(* Reduce the number of initial states.                                      *)
(* Some read-world invariant (here terminationDetected occurs within N steps  *)
(* where N has been chosen arbitrarily).                                    *)
(***************************************************************************)

CONSTANTS   Node,            \* The set of all nodes in the system.
            Init,            \* Fewer initial states to speed-up startup.
            TerminationDetected,  \* Some read-world invariant (here terminationDetected occurs within N steps where N has been chosen arbitrarily).
            PostInv          \* JsonInv
VARIABLES   c,               \* The communication channel between nodes.
            vc,              \* A vector clock for each node to keep track of the number of messages sent and received.
            m,               \* The message being transmitted by a node.
            n                 \* The current node in the system.
----------------------------------------------------------------------------
JsonInv ==    \* Format the error-trace as JSON and write to a file.
    /\ c = [n1 -> {(m1, vc1), (m2, vc2)}, n2 -> {(m3, vc3)}]
    /\ m = "Hello World!"
    /\ vc = [(n1, 0), (n2, 0)]
    /\ n = n1
    \* Format the error-trace as JSON and ping some web endpoint.
    /\ c = [n1 -> {(m1, vc1)}, n2 -> {(m3, vc3)}]
    /\ m = "Hello World!"
    /\ vc = [(n1, 0), (n2, 0)]
    /\ n = n1
    
Init == \* The initial predicate.
    /\ c = [Node -> {}]        \* Initialize the communication channel between nodes with empty channels.
    /\ vc = [Node -> []]       \* A vector clock for each node to keep track of the number of messages sent and received.
    /\ m = ""                \* The message being transmitted by a node.
    /\ n = Node              \* Initialize the current node in the system.
        
Spec == \* Rule 0 *)
EWD840 *)
/\ c'[n] = {(m, vc)}        \* Each node maintains a (local) vector clock.
/\ vc'[n] = [Node -> []]     \* Initialize the vector clock for each node to keep track of the number of messages sent and received.
/\ m' = ""                   \* The message being transmitted by a node.
/\ n' = Node                 \* Initialize the current node in the system.
        
PostInv ==    \* Some read-world invariant (here terminationDetected occurs within N steps where N has been chosen arbitrarily).
    /\ c'[n] = {(m, vc)}        \* Each node maintains a (local) vector clock.
    /\ vc'[n] = [Node -> []]     \* Initialize the vector clock for each node to keep track of the number of messages sent and received.
    /\ m' = ""                   \* The message being transmitted by a node.
    /\ n' = Node                 \* Initialize the current node in the system.
        
JsonInv ==    \* Format the error-trace as JSON and write to a file.
    /\ c = [n1 -> {(m1, vc1), (m2, vc2)}, n2 -> {(m3, vc3)}]
    /\ m = "Hello World!"
    /\ vc = [(n1, 0), (n2, 0)]
    /\ n = n1
    \* Format the error-trace as JSON and ping some web endpoint.
    /\ c = [n1 -> {(m1, vc1)}, n2 -> {(m3, vc3)}]
    /\ m = "Hello World!"
    /\ vc = [(n1, 0), (n2, 0)]
    /\ n = n1
    
CHECK_DEADLOCK FALSE
====