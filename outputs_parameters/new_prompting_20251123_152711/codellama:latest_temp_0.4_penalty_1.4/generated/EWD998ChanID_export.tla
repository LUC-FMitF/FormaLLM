---- MODULE EWD998ChanID_export ----

(**************************************************************************)
(* c properly initialized                                                *)
(* with empty channels.                                                   *)
(* Reduce the number of initial states.                                    *)
(* Some read-world invariant (here terminationDetected occurs within N steps*)
(\* where N has been chosen arbitrarily).                               *)
(**************************************************************************)

CONSTANTS Node = {n1, n2, n3, n4, n5, n6, n7}  \* The set of all nodes.
INITIAL_VECTOR clocks[Node] == [k |-> [] : k \in Node]   \* Initialize vector clocks for each node to empty channels.
                                /\ terminationDetected = FALSE    \* No detection yet.
----------------------------- SPECIFICATION ----------------------------
Spec == Init /\ TERMINATION_DETECTED  \* The simulator/generator may generate a prefix of a behavior whose length is less than what we wish to see.
                                \* This invariant will be violated if terminationDetected becomes TRUE within N steps, where N has been chosen arbitrarily.
----------------------------- INVARIANT ----------------------------
JsonInv == /\ JSON_INV(clocks)    \* The vector clocks are properly formatted as a json object with the node names and their corresponding channels.
PostInv == terminationDetected => FALSE   \* If termination has been detected, it should not be reported again in subsequent steps of the simulation/generation process.
----------------------------- CHECK_DEADLOCK ----------------------------
FALSE  \* Do NOT check for deadlocks during TLC's search for a counterexample to an invariant violation. This will speed up the execution time significantly, but may lead to some false negatives in case of real errors. *)
====