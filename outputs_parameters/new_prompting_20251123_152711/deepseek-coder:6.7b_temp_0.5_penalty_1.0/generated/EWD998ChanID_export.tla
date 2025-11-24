---- MODULE EWD998ChanID_export ----

(**************************************************************************)
(* c properly initialized with empty channels. *)
(* Reduce the number of initial states. *)
(* Some read-world invariant (here terminationDetected occurs within N steps *)
(* where N has been chosen arbitrarily). *)
(* Make TLC stop and print the usual error trace. *)
(* Each node maintains a (local) vector clock *)
(* https://en.wikipedia.<｜begin▁of▁sentence｜>.org/wiki/Vector_clock *)
(* Format the error-trace as JSON and write to a file. *)
(* Format the error-trace as JSON and ping some web endpoint. *)
(**************************************************************************)

CONSTANTS Node, Init \* Fewer initial states to speed-up startup.

VARIABLES VectorClock \* Each node maintains a (local) vector clock

(* The simulator/generator may generate a prefix of a behavior whose length is *)
(* less than what we wish to see. *)
CHECK_DEADLOCK FALSE

(* JsonInv: A read-world invariant that ensures the termination of the system *)
PostInv == [](VectorClock[n] = 0 : Node)

(* Spec: The specification of the system *)
Spec == [](VectorClock[n] = 0 : Node) /\ ... /\ ...

(* Init: The initial state of the system *)
MCInit == [](VectorClock[n] = 0 : Node) /\ ... /\ ...

(* The next state relation *)
Next == [](VectorClock[n]' = VectorClock[n] + 1 : Node) /\ ... /\ ...

(* Initialize state with Init and transition with Next *)
Spec == Init /\ [](Next)

=============================================================================
====

CONSTANTS
    Node = {n1,n2,n3,n4,n5,n6,n7}
    Init <- MCInit

SPECIFICATION
    Spec

INVARIANT
    PostInv

CHECK_DEADLOCK
    FALSE
====