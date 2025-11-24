---- MODULE EWD998ChanID_export ----

(******************************************************************************)
(* This is a simple model of vector clocks in distributed systems. Each node   *)
(* maintains a local vector clock, which tracks the state of each other node at *)
(* various points in time.                                                     *)
(******************************************************************************)

CONSTANTS Node = {n1, n2, n3}  (* The set of all nodes *)
VARIABLES Clock[Node]           (* A vector clock for every node *)

Init == \* Initial state predicate. Each clock starts at time zero.
    /\ [n \in Node |-> Clock[n] = 0]
    
Next == \* Next-state relation. On each step, a random node increments its own clock.
    \[Clock EXCEPT @ 1 + Clock[\@]]_<<Node>>

Spec == Init /\ [][Next]_(<vars>) (* Initial state and transition with next *)
    
PostInv == \* Post-invariant: All clocks are nonnegative at all times.
    /\ [[n \in Node |-> 0 <= Clock[n]]_<<Node>>]
        
JsonInv == \* JSON invariant for error trace formatting and writing to file *)
     { "error": [{ "node": n, "clockTime": Clock[n]} : n IN Node ] } 
     
===============================================================================
====
(* TLC Configuration: *)
CONSTANTS Init = MCInit (* Use Moore-based initial states for speedup. *)
SPECIFICATION Spec  
INVARIANT PostInv /\ JsonInv   
CHECK_DEADLOCK FALSE  (* No deadlock check, as this is a simple model of vector clocks *)
===============================================================================
====