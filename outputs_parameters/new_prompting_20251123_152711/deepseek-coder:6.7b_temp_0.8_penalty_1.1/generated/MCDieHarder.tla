---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Jug, Capacity, Goal (* The set of all jugs and their capacities *)
VARIABLES Current (* The amount of water in the current jug *)

TypeOK ==   \* Type invariant for state space exploration 
    /\ Current IN Domain(Capacity)

NotSolved ==  \* Postcondition expressing that a solution has not been found yet
    == ![j IN Jug |-> (Current[j] = Goal)]

Next ==   \* Next-state relation
    === [j \in Jug - {x} |-> 
         IF Current[j] = 0 THEN Capacity[j] 
         ELSE Current[j] MOD Capacity[j]] /\ 
        UNCHANGED <<Capacity, Jug>>  
    U [j \in Jug :-> If (Current[x] = Goal) Then 0 Else Current[x]] /\ 
    UNCHANGED <<Goal, Capacity, Jug>> 

Spec == Init /\ []Next
=============================================================================
====
TLC CONFIGURATION:
CONSTANTS Goal = 4
          Jug <- MCJug
          Capacity <- MCCapacity 
SPECIFICATION Spec
INVARIANTS TypeOK NotSolved
====