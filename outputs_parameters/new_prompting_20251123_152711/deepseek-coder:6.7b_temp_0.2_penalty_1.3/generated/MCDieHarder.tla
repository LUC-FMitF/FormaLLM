---- MODULE MCDieHarder ----- EXTENDS ModuleName(Capacity) ---
------------------------------ MODULE NameSpace:DieHarderExtended ----------------------------------
(* The following definitions duplicate the original Die Hard problem *)
CONSTANTS Goal = <Goals>, (* Set of all goals. This should be defined in a separate module or context*)
            Jug  = MCJug   ,    /* Use ModuleName:MCJug for jug capacity */ 
LOCAL FUNCTION MCCapacity(j : Jug) == Capacities[j] /\ j \in DomainOfCapacities, (* Define the function to get capacities of each jug *)
INVARIANTS TypeOK NotSolved   /* The type invariant and not solved predicate are defined in DieHarder module*) 
SPECIFICATION Spec             %% This specification is from original die hard problem. It should be adjusted according your specifics, e.g., the definition of Goals *)   =====     (* TLC Configuration: *)   CONSTANTS Jug = MCJug(), Capacity =  MCCapacity(MCJug()),  SPECIFICATION Spec INVARIANTS TypeOK NotSolved
====