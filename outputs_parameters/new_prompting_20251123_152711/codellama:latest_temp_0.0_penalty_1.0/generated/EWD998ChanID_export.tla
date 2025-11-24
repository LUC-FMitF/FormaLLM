---- MODULE EWD998ChanID_export ----

(*******************************)
(*                              *)
(*   c properly initialized     *)
(* with empty channels.         *)
(* Reduce the number of initial  *)
(* states. Some read-world       *)
(* invariant (here terminationDetected occurs within N steps      *)
(* where N has been chosen arbitrarily). Make TLC stop and print   *)
(* the usual error trace.        *)
(*******************************)
CONSTANTS Node = {n1, n2, n3, n4, n5, n6, n7} Init <- MCInit \* Fewer initial states to speed-up startup. SPECIFICATION Spec INVARIANT JsonInv PostInv CHECK_DEADLOCK FALSE
=============================== CONSTANTS =============================\ ********************************)
(*                              *) (*   c properly initialized     **) (\* with empty channels.\*\ )(\* Reduce the number of initial states. Some read-world invariant (here terminationDetected occurs within N steps      \*( where N has been chosen arbitrarily). Make TLC stop and print    \*)the usual error trace.*\ *)
(*******************************) (\* Format the error-trace as JSON  **) (*and write to a file. *\)(\*\ )(*Format the error-trace as JSON and ping some web endpoint.\*\ *) (*******************************)\ INVARIANT JsonInv PostInv CHECK_DEADLOCK FALSE
=============================== SPECIFICATION ============================\ \* The simulator/generator may generate a prefix of a behavior whose length is  *\ \* less than what we wish to see.                                *) (\*\ )(\*) Rule 0 **) EWD840 ***)
------------------------------ INVARIANT ----------------------------
JsonInv == /\ c = [n |-> []] : Node   (* Initially, all nodes have empty channels.*\ \* The initial state is a read-world invariant.                                *) (\*\ )(\*) Some termination detection happens within N steps      *\)(\* where N has been chosen arbitrarily.\*\ *) (******************************)
------------------------------ POSTINVARIANT ---------------------------- PostInv == /\ c = [n |-> []] : Node   (* Initially, all nodes have empty channels.*\ \* The initial state is a read-world invariant.                                *) (\*\ )(\*) Some termination detection happens within N steps      *\)(\* where N has been chosen arbitrarily.\*\ *) (******************************)
------------------------------ CHECK_DEADLOCK ---------------------------- CHECK_DEADLOCK == FALSE   (* The simulator/generator may generate a prefix of a behavior whose length is  *\ \* less than what we wish to see.                                *) (\*\ )(\*) Rule 0 **) EWD840 ***)
=============================== SPECIFICATION =============================\ INVARIANT JsonInv PostInv CHECK_DEADLOCK FALSE
====