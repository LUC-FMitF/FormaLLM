---- MODULE EWD687a_anim ----

(***************************************************************************)
(* Increasing refX moves the arrowhead to the middle of the line away from    *)
(* the tip. NodeDimension ought to be divisible by 2 for proper alignment     *)
(* of nodes and edges. round (rx=15) if node is active. A solid, black       *)
(* line with an arrow at its tip denotes an edge. %%03d to escape %03d in    *)
(* Java format strings.                                                     *)
(***************************************************************************)
LOCAL CONSTANT refX = 15; (* Increasing this moves the arrowhead closer to the middle of the line *)
LOCAL CONSTANT NodeDimension = ... ; (* Must be divisible by 2 for proper alignment of nodes and edges *)
...
(* Define your invariants, specification here. Assuming they are defined elsewhere in the module*)
\* TypeOK: Your type invariant definition *\)
TypeOK == \*(Your Definition Here)*\
DT1Inv  == (* DT1Invariant definition goes here *) 
InterestingBehavior ==  (* Interesting behavior definition goes here *)
...
(* Define your properties, aliases and check deadlock conditions*)
PROPERTY DT2 := (* Property DT2 definition goes here *)
\* CountersConsistent: Your counter consistent property *\)
CountersConsistent == \*(Your Definition Here)*\ 
TreeWithRoot ==  (* Tree with root condition definition goes here *)
StableUpEdge  == (* Stable up edge condition definition goes here *)
...
(* Define your action constraints*)
ACTION_CONSTRAINT NoSuperfluousIdleSteps := \*(Your Definition Here)*\ 
CHECK_DEADLOCK FALSE ==> (DT1Inv /\ ... ) (* Deadlock check constraint, assuming other conditions are defined elsewhere in the module *)
...
(* Define your nodes of network and edges*)
NodesOfNetwork = {L, P1, P2, P3, P4, P5} 
Edges == SUBSET ({ n \in NodesOfNetwork X NodesOfNetwork : (* Your edge condition definition goes here *) })  
...
(* Define your functions and operations*)
YourFunctionName(...) = ... (* Function definition goes here *)
OperationName =  (* Operation definition goes here *) 
...
=============================================================================
====