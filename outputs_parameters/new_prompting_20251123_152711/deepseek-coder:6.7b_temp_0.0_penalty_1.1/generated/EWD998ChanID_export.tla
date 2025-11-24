---- MODULE EWD998ChanID_export ----

(**************************************************************************)
(* c properly initialized with empty channels. Reduce the number of initial *)
(* states. Some read-world invariant (here terminationDetected occurs within N*)
(* steps where N has been chosen arbitrarily). Make TLC stop and print the   *)
(* usual error trace. Format the error-trace as JSON and write to a file.    *)
(* Format the error-trace as JSON and ping some web endpoint.               *)
(**************************************************************************)

CONSTANTS Node, Init \* The set of all nodes in the system.
VARIABLES Clock \* A vector clock for each node.

Init == ...  (* Fewer initial states to speed-up startup. *)

Next == ...  (* Operators for state transitions. *)

Invariant1 == ...  (* Some read-world invariant. *)
PostInv == ...  (* Post condition invariant. *)

Spec == Init /\ []Next \* The specification.

CHECK_DEADLOCK FALSE  (* The simulator/generator may generate a prefix of a *)
                     (* behavior whose length is less than what we wish to see. *)
=============================================================================
====

(* TLC Configuration *)
CONSTANTS Node = {n1, n2, n3, n4, n5, n6, n7}
INITIALISATION MCInit (* Fewer initial states to speed-up startup. *)
SPECIFICATION Spec
INVARIANT JsonInv  (* Some read-world invariant in JSON format. *)
           PostInv  (* Post condition invariant. *)
CHECK_DEADLOCK FALSE  (* The simulator/generator may generate a prefix of a *)
                       (* behavior whose length is less than what we wish to see. *)
====