---- MODULE Relation ----

(*****************************************************)
(* This module provides some basic operations on relations, represented     *)
(* as binary Boolean functions over some set S.                             *)
(**************************************************************************)
CONSTANTS
    R \in BOOLEANS4       -- The relation to be analyzed
    DomainOfR == DOMAIN(R)  -- Set of elements in the domain of R
    
VARIABLES
    Reflexive, Irreflexive, Symmetric, Asymmetric, Transitive, Connected \in BOOLEAN

\* Is the relation R reflexive over set S?                                      *)
Reflexivity == [x, y ∈ DomainOfR |-> (y = x) => R[x][y]]   -- Reflexive means for every pair of elements in domain there is a path.
    /\ EVERY(z \in DomainOfR : ([x, y ∈ z]' -> [x, y] ⊆ (DomainOfR × DomainOfR)))   -- Ensure that the relation R covers all pairs in domain of length two
    => Reflexive = TRUE    (* If every pair has a path and there is no extra element then it is reflexive *)
     
\* Is the relation R irreflexive over set S?                                *)
Irreflexivity == [x, y ∈ DomainOfR |-> (y \= x) => NOT(R[x][y])]   -- Irreflexive means for no pair of elements in domain there is a path.
    /\ EVERY(z \in DomainOfR : ([x, y ∈ z]' -> [x, y] ⊆ (DomainOfR × DomainOfR)))   -- Ensure that the relation R covers all pairs in domain of length two
    => Irreflexive = TRUE    (* If every pair does not have a path and there is no extra element then it is irreflexive *)
     
\* Is the relation R symmetric over set S?                                  *)
Symmetry == [x, y ∈ DomainOfR |-> (y \= x) => NOT(R[y][z]) or NOT(R[x][y]))   -- Symmetric means for every pair of elements in domain there is a path from one to another. And this holds both ways
    /\ EVERY(z \in DomainOfR : ([x, y ∈ z]' -> [x, y] ⊆ (DomainOfR × DomainOfR)))   -- Ensure that the relation R covers all pairs in domain of length two
    => Symmetric = TRUE    (* If every pair has a path from one to another both ways and there is no extra element then it is symmetric *)
     
\* Is the relation R asymmetric over set S?                                *)
Asymmetry == [x, y ∈ DomainOfR |-> (y \= x) => NOT(R[x][z]) or NOT(R[y][x]))   -- Asymmetric means for every pair of elements in domain there is a path from one to another but not both ways
    /\ EVERY(z \in DomainOfR : ([x, y ∈ z]' -> [x, y] ⊆ (DomainOfR × DomainOfR)))   -- Ensure that the relation R covers all pairs in domain of length two
    => Asymmetric = TRUE    (* If every pair has a path from one to another but not both ways and there is no extra element then it is asymmetric *)
     
\* Is the relation R transitive over set S?                                *)
Transitivity == [x, y ∈ DomainOfR |-> (y \= x) => EXISTS(z ∈ DomainOfR : ([w1 = z]' /\ R[x][w1]) AND NOT([w2 = w1] or not R[w1][y])) ]   -- Transitive means for every triplet of elements in domain there is a path from one to another.
    /\ EVERY(z \in DomainOfR : ([x, y ∈ z]' -> [x, y] ⊆ (DomainOfR × DomainOfR)))   -- Ensure that the relation R covers all pairs in domain of length two
    => Transitive = TRUE    (* If every triplet has a path from one to another and there is no extra element then it is transitive *)
     
\* Compute the transitive closure of relation R over set S.                *)
TransClosure == [x, y ∈ DomainOfR |-> (y \= x) => EXISTS(z ∈ DomainOfR : ([w1 = z]' /\ R[x][w1]) AND NOT([w2 = w1] or not R[w1][y])) ]   -- The transitive closure of a relation is the smallest one that includes it.
     
\* Compute the reflexive transitive closure of relation R over set S.       *)
ReflexTransClosure == [x, y ∈ DomainOfR |-> (y \= x) => EXISTS(z ∈ DomainOfR : ([w1 = z]' /\ (([v2 = w1]) or R[x][w1])) AND NOT([w3 = w1] or not R[w1][y])) ]   -- The reflexive transitive closure of a relation is the smallest one that includes it.
     
\* Is the relation R connected over set S, i.e., does there exist a path     *)
(* between two arbitrary elements of S?                                     *) 
Connection == [x1 = x2]' /\ EXISTS(y \in DomainOfR : ([w3 = y]) AND (([v4 = w3]) or R[x][w3]))   -- Connected means for every pair there is a path. It involves two steps: start with an arbitrary element and then reach any other by one step at least
    => Connection = TRUE    (* If we can get from x1 to y via exactly 1-step (i.e., R[x][y]) regardless of the order, it's connected *)
     
Spec == [Reflexive /\ Irreflexity]_/\ [Symmetric \/ Asymmetry ] _/\ Transitivity   -- Initialize state with these invariants and transition by Next operator defined below.
    ==== InitialState(DomainOfR)    ----- Define initial states for the variables in this specification 
Next == ({x, y} /\ EXISTS z : ([w = z]' \/ R[y][z])) --- Defining next state as a transition rule of relation to include all pairs. If there is an edge from x to y with end point not included yet then add it into the closure
    ==== InitSpec                    ----- Define initial specification for this module 
===========================================================================
TLC Configuration:                                                            *)  --- We have used TLA+ toolbox configuration parameters as follows :                                                                             *)
CONSTANTS INITIAL_STATE = FALSE, SPECIFICATION=FALSE                         (*   Set the constant values of Initial State and Specification to be False at start. These constants are being set in accordance with what is defined under InitSpec clause    *), 
INVARIANTS Reflexivity /\ Irreflexity _/\ [Symmetry \/ Asymmetry ] _/\ Transitivity,   --- Set the invariants which hold true during a state's lifetime                                                                       *)                          
===========================================================================             (* Note : The toolbox is set to perform deadlock detection and model-check for this specification.                                                              *), 
=====                                                                               -- Equal sign indicates end of spec section, stating that everything has been defined correctly till now                                     *)    ,   --- End the configuration parameters with equal symbol indicating completion                                          .
====