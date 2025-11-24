---- MODULE EWD687a_anim ----

(***************************************************************************)
(* This is a description for the module EWD687a                            *)
(*                                                                         *)
(* It includes all the definitions, properties, invariants, actions,       *)
(* aliases and constraints needed to describe a TLA+ system.                *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences

\* Defines the set of nodes in the network
NodesOfNetwork == {L, P1, P2, P3, P4, P5}

\* Generates a random subset of edges based on the nodes in the network.
Network == LET Edgs == SUBSET [ n \in NodesOfNetwork : 
    \* No self-loops.
    /\ n[1] # n[2]
    \* L is not a sink.
    /\ n[2] # L ] 
IN TLCEval(RandomElement(Edgs))

\* ASSUME PrintT(<<"Edges", Edges>>) - prints the randomly chosen set of edges.

SPECIFICATION Spec == ... (* Your specification goes here *)

\* Defines invariants for your system.
INVARIANT TypeOK == ... (* Your type invariant goes here *)
INVARIANT DT1Inv == ... (* Invariant 1 goes here *)
INVARIANT InterestingBehavior == ... (* An interesting behavior invariant goes here *)

\* Defines properties for your system.
PROPERTY DT2 == ... (* Property 2 goes here *)
\* PROPERTY CountersConsistent == ... (* A property to ensure counters are consistent goes here *)
\* PROPERTY TreeWithRoot == ... (* A property ensuring the tree has a root goes here *)
\* PROPERTY StableUpEdge == ... (* A property ensuring stable up edges in the overlay tree goes here *)

\* Defines aliases for variables.
ALIAS Alias == LET x == Procs[1], y == Procs[2] IN [x: Nat, y: Nat] 

\* Checks for deadlock situations in your system.
CHECK_DEADLOCK FALSE 

\* Defines constraints on actions.
ACTION_CONSTRAINT NoSuperfluousIdleSteps == 
    \* Stops the process if it remains idle for too long.
    /\ IF Idle AND Pre[n](Active) THEN NOT Last[n](Idle) 

=============================================================================
====