---- MODULE EWD998ChanID_export ----

(**************************************************************************)
(* c properly initialized                                                *)
(* with empty channels.                                                   *)
(* Reduce the number of initial states.                                    *)
(* Some read-world invariant (here terminationDetected occurs within N steps  *)
(* where N has been chosen arbitrarily).                                     *)
(* Make TLC stop and print the usual error trace.                            *)
(* Make TLC stop and print the usual error trace.                           *)
(**************************************************************************)

CONSTANTS   Node,       \* The set of all nodes in the system.
            Init,       \* Fewer initial states to speed-up startup.
            Terminated  \* A node has terminated if it is not running any more.
VARIABLES   c,          \* A clock for each node.
            channels    \* The set of all communication channels between nodes.
------------------------------------------------------------------------------
JsonInv ==     \* Json invariant: the error trace as JSON and written to a file.
    /\ [](c = 0)                   \* c is initially zero for each node.
    /\ \A n \in Node :             \* Some read-world invariant (here terminationDetected occurs within N steps where N has been chosen arbitrarily).
        \E <<n>> \* At least one event in the trace from a given node.
            [terminationDetected |-> TRUE]                   \* The node is terminated if it does not run any more.
    /\ UNCHANGED channels                                  \* No communication channel has been created yet.
    
PostInv ==      \* Post-state invariant: the error trace as JSON and ping some web endpoint.
    /\ [](c = 0)                   \* c is initially zero for each node.
    /\ \A n \in Node :             \* Some read-world invariant (here terminationDetected occurs within N steps where N has been chosen arbitrarily).
        \E <<n>> \* At least one event in the trace from a given node.
            [terminationDetected |-> TRUE]                   \* The node is terminated if it does not run any more.
    /\ UNCHANGED channels                                  \* No communication channel has been created yet.
    
Spec ==       \* Rule 0 *)
    Init <=
        <<>>, [c = 1], [terminationDetected |-> FALSE]
------------------------------------------------------------------------------
THEOREM Spec => JsonInv /\ PostInv                         
=============================================================================
====