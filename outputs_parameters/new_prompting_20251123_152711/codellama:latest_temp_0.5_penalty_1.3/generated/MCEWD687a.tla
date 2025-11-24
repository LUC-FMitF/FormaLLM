---- MODULE MCEWD687a ----

(**************************************************************************)
(* A distributed tree with leader election and concurrent insertions.     *)
(**************************************************************************)

CONSTANTS   L,       \* The number of nodes in the tree.
            P1,      \* Proposer 1's ID.
            P2,      \* Proposer 2's ID.
            P3        \* Proposer 3's ID.
VARIABLES   Procs,    \* MV CONSTANT definitions @modelParameterConstants:Procs
            Edges,    \* MV CONSTANT definitions @modelParameterConstants:Edges
            Leader,   \* MV CONSTANT definitions @modelParameterConstants:Leader
            
CONSTRAINT  constr_1633116534008313000    \* CONSTRAINT definition @modelParameterContraint:0
            TypeOK,                       \* INVARIANT definition
            DT1Inv,                       \* INVARIANT definition
            
SPECIFICATION   Spec                      \* SPECIFICATION definition
CHECK_DEADLOCK    FALSE                   \* CHECK_DEADLOCK definition
------------------------------ PROPERTY definitions --------------------------
PROPERTIES
    CountersConsistent,         \* StableUpEdge
    TreeWithRoot                \* Property name
=============================================================================
====