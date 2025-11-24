---- MODULE EWD687a_anim ----

(***************************************************************************)
(* Increasing refX moves the arrowhead to the middle of the line away from    *)
(* the tip.                                                                 *)
(* NodeDimension ought be divisible by 2 for proper alignment of nodes and edges.*))
(* ... more comments here ...                                                 *)
(******************************************************************************)

CONSTANTS L = <L details>, P1 = <P1 details>, P2 = <P2 details>, P3 = <P3 details>, 
            P4 = <P4 details>, P5 = <P5 details>  (* Define all symbols before use *)

(* ... more comments here ...                                                 *)
(******************************************************************************)

CONSTANT NodesOfNetwork == {L, P1, P2, P3, P4, P5}  (* The set of nodes in the network.   *)
     Edges = <edges details>                             (* Defining edges for your graph.    *)
(* ... more comments here ...                                                 *)
(******************************************************************************)
LOCAL NodesOfNetwork - (Edges \X SUBSET 2 ## {<x,y> ∈ dom(NodesOfNetwork)}) 
          == {} (* No self-loops and no isolated nodes.                            *)
(* ... more comments here ...                                                 *)
(******************************************************************************)

LOCAL INSTANCE FiniteSets   (* Define all symbols before use                     *)
LOCAL INSTANCE Naturals    (* Define all symbols before use                     *)
LOCAL INSTANCE Sequences 
(* ... more comments here ...                                                 *)
(******************************************************************************)

\* Defines the specification and invariants of your module.                    \*)  
SPECIFICATION Spec == <Spec details> (* Define all symbols before use             *)      
INVARIANT TypeOK               == <TypeOK details> 
      DT1Inv                  == <DT1Inv details>       
      InterestingBehavior     == <InterestingBehavior details>   
(* ... more comments here ...                                                 *)  
(******************************************************************************)
====