---- MODULE EWD998ChanID_export ----

(****************************************************************************)
(* This module defines the operations and invariants for a vector clock, which *)
(* is used in the context of distributed systems. A vector clock is a data   *)
(* structure that records the state of each process (or node) over time. It's  *)
(* an extension of Lamport timestamps and includes a counter for each node.    *)
(****************************************************************************)

EXTENDS FiniteSets, Naturals, Integers

CONSTANTS   Node,              \* The set of all nodes in the system.
            Init               \* Initial state predicate.
VARIABLES   clock,             \* A vector clock recording the state of each node.
            msg                \* Messages sent between nodes.

Init ~~>     \* The initial state predicate.
    /\ clock = [n ∈ Node |-> 0]       \* Initialize all counters to 0.
    
Next ~~>     \* The next-state relation.
    /\ clock'[sender(msg)] = clock[sender(msg)] + 1        \* Increment the sender's counter.
    /\ clock'[receiver(msg)] = max{clock[receiver(msg)], msg[receiver(msg)]}       \* Update the receiver's counter.
    
Spec ~~>     \* The specification.
    Init /\ []Next

PostInv ~~>   \* Post-state invariant.
    clock[n] >= 0 forall n in Node      \* All counters are nonnegative.

JsonInv ~~>   \* Json invariant.
    To_JSON(clock) is a valid JSON object     \* The vector clock can be serialized to JSON.

CHECK_DEADLOCK FALSE       \* Disable deadlock detection, as this module does not model inter-process synchronization.
=============================================================================
====
### Instruction:<｜begin▁of▁sentence｜>
# Comments:
c properly initialized
with empty channels.
Reduce the number of initial states.
Some read-world invariant (here terminationDetected occurs within N steps
where N has been chosen arbitrarily).
Make TLC stop and print the usual error trace.
Make TLC stop and print the usual error trace.
Rule 0 
EWD840 
Each node maintains a (local) vector clock 
https://en.wikipedia.org/wiki/Vector_clock 
Format the error-trace as JSON and write to a file. 
Format the error-trace as JSON and ping some web endpoint.
====