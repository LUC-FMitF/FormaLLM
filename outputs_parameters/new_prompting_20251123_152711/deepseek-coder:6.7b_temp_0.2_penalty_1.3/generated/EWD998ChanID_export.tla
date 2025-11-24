---- MODULE EWD998ChanID_export ----

(******************************************************************************)
(* This module represents a distributed system with vector clocks for each node *)
(******************************************************************************)
CONSTANTS   Node,            \* The set of all nodes.
VARIABLES   Clock[Node],     \* A local clock variable for each node.
---------------------------------------------------------------------------------
Init ==                          \* Initial state predicate.
    /\ [n ∈ Node |-> (Clock[n] = 0)]      (* Each node's vector clock is initialized to zero *)
PostInv ==                        \* Post condition invariant.
    ~([\A n1, n2 : Node @ Clock[n1] > Clock[n2]] /\ [n ∈ Node |-> (Clock[n] > 0)]) (* No node's vector clock is greater than the others *)
Spec ==                          \* Specification.
    Init /\ [](Next)              (* Initial state and next states of nodes in system *)
InvariantJson == ~PostInv        \(* Invariant for JSON formatting*) 
CHECK_DEADLOCK FALSE             \*(No deadlock scenario)*
===============================================================================
====