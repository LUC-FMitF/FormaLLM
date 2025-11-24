---- MODULE EWD687a_anim ----

(* This module models a distributed system of processes with an underlying network topology *)

EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NodeDimension == 10    (* Divisible by 2 for proper alignment of nodes and edges.*)
LOCAL CONSTANT RoundRx == 15   (* Increasing refX moves the arrowhead to the middle *)
                              (* of the line away from the tip.                     *)
CONSTANT Active == {L, P1, P2, P3, P4, P5}  (* A set containing active processes      *)
LOCAL CONSTANT Edges = ...     (* The network edges as a subset definition         *)
                              (* This is specific to your model and should be defined*)
                              (* in the context of this module                      *)
CONSTANT Leader == L          (* The leader process                                *) 
                              
\* Processes are identified by their name: P1, P2 etc. *\)  
PROCEDURE NodeName[proc] ==  -- Name of a node given its state number 
    CASE proc MOD (Cardinality(Active)) OF {0 -> L , \_MOD\_ ->  Active\}     
\* Action from predecessor to successor: the edge action *\)  
PROCEDURE EdgeAction[proc1, proc2] ==  -- Name of an edge given its source and destination 
    CASE (proc2 MOD (Cardinality(Active))) OF {0 -> "" , \_MOD\_ ->  Edges\}    
\* Positioning: coordinates chosen according to the layout algorithm *\)  
PROCEDURE Pos[node] == -- Coordinates for a node 
    CASE node OF \{L -> [NodeDimension, NodeDimension], P1 -> [0,0]}      (* This is *)
\* A specific network of processes: nodes connected by edges *\)  
PROCEDURE Network ==  UNION {[proc1, proc2] :  proc1 \in Active , proc2 \in Active}    
LOCAL CONSTANT NodeShape == -- The shape and color for each node in the visualization    *)
                 \{L -> (NodeDimension/4..3*NodeDimension/4, NodeDimension/4..3*NodeDimension/4), 
                  P1->  [0,2],P2->  [0,6]\}   (* Example shape and color definitions *)   
PROCEDURE EdgeAction == -- Action on an edge from source to target node                  
                 \{[L ,P1]-> "Send" | ([P1  U {n \in Active : n /= P2} ],P2)->  "Receive"}   (* Example action definitions *)   
\* Animated GIF visualization: SVG frame for each TLA+ state *\)      
PROCEDURE Visuals == -- Visual representation of a node in the animation 
                 \{proc -> IF NodeName(proc) = L THEN "Leader"   (* Example definitions *)    
                           ELSE IF ActiveNodes[NodeShape, proc] THEN ""      (* Rectangle shape for active nodes. Empty string otherwise*)   
                           FI\}      
PROCEDURE Animation == -- The SVG frame as a visualization of the current TLA+ state 
                 <<"<svg>", Visuals(proc), EdgesVisual, Legend>>     (* Example composition *)  
\* A black square denotes an idle process, a red circle for active ones *\)     
PROCEDURE NodeShape[node] ==  -- Shape of the node visualization 
                 IF ActiveNodes THEN "Rectangle" ELSE ""       (* Black rectangle means Idle*)   
     \*\* An SVG group containing rectangles denoting nodes. Approximately at center *)
\* Processes name *\)  
PROCEDURE NodeName == -- The processes' names 
                 \[node -> CASE node OF \{L->  "Leader", P1,P2,...,Pn\}      (* Example definitions *)    \}      
LOCAL CONSTANT LeaderPos = [NodeDimension/4..3*NodeDimension/4 , NodeDimension/4]   -- Position of the leader  in the visualization.    
\* A specific network of processes: nodes connected by edges *\)     
PROCEDURE Network ==  UNION {[proc1, proc2] :  (proc1 \in Active ) /\ (proc2 \in Active) }    (* Example edge definitions *)  
LOCAL CONSTANT Visuals = <<"rectangle", NodeShape(node),Pos(NodeName(node))>> -- The visual representation of a node in the animation.      
     \(* Animated GIF visualization: SVG frame for each TLA+ state *\)     
PROCEDURE EdgeAction ==   /\  [proc1, proc2] \in Network -> "Send"|->  "Receive",         (* Example action definitions *)    \}      
LOCAL CONSTANT Animation = <<Animation>> -- The SVG frame as a visualization of the current TLA+ state.     
     \(* Legend with four rows of labels whose top left point is at BasePos *\)  
PROCEDURE Visuals == -> IF NodeName(node)= L THEN "Leader" ELSE ""       (* Black rectangle means Idle*)    \}       
\* An SVG group containing lines denoting the edges. A line connecting a from and to node *)
\* is annotated with three labels: at mid-point of line, integer indicates number  *\)  
(* CountersConsistent -> True if counters are consistent throughout network*)   
LOCAL CONSTANT TypeOK == [proc1 , proc2] \in Network /\ EdgeAction(proc1)= "Send" IFF (* Example definitions *)     
     NodeName[EdgeDestinationNode] = ""  -- The destination node is idle.  
(* TreeWithRoot -> True if there exists an up-edge from the leader to every other process*)   
LOCAL CONSTANT InterestingBehavior == EXISTS {proc \in Active} [Leader, proc ] /\      (* Example definitions *)    
     NodeName[EdgeDestinationNode]= Pn  -- The destination node is active.  
(* StableUpEdge -> True if for each process p there exists a stable up-edge*)   
LOCAL CONSTANT DT1Inv == [proc \in Active} EXCEPTIONS (p) == 0     (* Example definitions *)      
\* NoSuperfluousIdleSteps : Actions from one state to another should have at least  *\)  
(* a superlative step.                                                               *)   
LOCAL CONSTANT DT2 == [proc1 , proc2] \in Network /\ EdgeAction(proc1)= "Send" IFF (* Example definitions *)     
     NodeName[EdgeDestinationNode] = ""  -- The destination node is idle.  
(* Animated GIF visualization: SVG frame for each TLA+ state *\)   
LOCAL CONSTANT CheckDeadlock == FALSE                                  (* Deadlocks are not allowed in this model*)      
\* Aliases to help keep the code clean and readable                       *)    
CONSTANT MsgCount = \(p \in Active : Count\{m | m /= ""\} OF NodeName[EdgeDestinationNode])\)   -- Number of unacknowledged messages on an edge. 
\* https://animator.tlapl.us interactively explore the animation *\)   
PROCEDURE Animation == -> IF WriteToFile(Animation, n) THEN "Write successful" ELSE "Failed to write file."       (* Example definitions *)     
(* The resulting set of EWD687a_anim_*.svg files can be rendered as an animated gif with:  *\)   
LOCAL CONSTANT Animation == -- Command for rendering the animation  
                 "$ convert -delay 100 -density 200 ./*.svg EWD687a.gif"       (* Example definition *)     
(* Please note that this is a very basic model and can be expanded upon with additional    *\)    
\* specifications, invariants, actions based on your requirements                  *)        
---- END NetworkModel ----
====