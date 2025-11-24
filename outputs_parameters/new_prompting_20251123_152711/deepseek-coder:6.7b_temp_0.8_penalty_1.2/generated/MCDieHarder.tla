---- MODULE DieHarder  ----
(******************************************************************************)
(* This model of 'Die Hard' as described in "Let's Make a Movie"               *)
(* assumes that Jug is the set containing all possible volumes of water         *)
(* contained by each jug, Capacity represents the volume of water in both      *)
(* jags at any given time.                                                    *)
(******************************************************************************)

CONSTANTS  Goal     \* The target amount to measure (water).
            Jug      = {10,5}    \* Different jug capacities.
VARIABLES   Capacity = MCCapacity(* Initialization of capacity depends on goal * )
            
NOT_Solved == \* No unsolved states means we have found a solution 
     /\ ~(Next[Capacity]= <<>>)  --> Next[] not empty, so there are still jugs to fill.  
      [ x in Jug |-> 0 ] = Capacity        (* The capacities of the jags should match our goal *)   
                      
MCCapacity (j1, j2 ) == \* Determines capacity by considering Goal 
     IF Cardinality(Jug) = 3 /\ ~((Goal in Jug)* (Cardinality({x | x in Jug & x<>0})>=2))   (* Case when we have more than one jug with volume different from zero *)
       THEN [j1, j2] = { Goal }  -->(if either of the capacity is equal to goal then return that)   
               /\ <<>> in (Next[Capacity])     -->  if next state is empty after filling one more jug   (* we are done *)        
       ELSE [j1, j2] = {Goal - Cardinality({x | x in Jug & x<>0}) }  UNION { Goal}    --> (Otherwise fill the remaining capacity)
     FI     
         
Spec == /\ Init[Capacity](MCCapacity(1,5))   (* Initialization of capacities *)      
          ~[](Next[\E x \in Jug : MCCapacity'(x)] = Next[(Capacity - {Goal})])         --> (Transition relation)     
             /\ NotSolved                   --->  No unsolved states   (* We are done when there is no remaining capacity to fill *)   
          
===============================================================================      
====  CONFIGURATION FOR TLC
(* Substitution of constants for parameters in the module DieHarder:         *)    
CONSTANTS Goal = 4                                                         
          Jug <- MCJug                                                                                   
LOCAL VARIABLES MCCapacity' == [j1, j2] = {Goal} --> (if either of jug capacity is equal to goal then return that) /\ <<>> in Next[Capacity](MCCapacity'(j1),MCCapacity'(j2)) (* we are done *)
===============================================================================