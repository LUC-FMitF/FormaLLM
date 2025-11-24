---- MODULE MCEWD687a ----

(***************************************************************************)
(* A distributed tree with a leader node.                                    *)
(***************************************************************************)
CONSTANTS   L,      \* The number of nodes in the system.
            P1,     \* The first process ID.
            P2,     \* The second process ID.
            P3       \* The third process ID.
VARIABLES   Procs,  \* MV CONSTANT definitions: Processes.
            Edges,  \* MV CONSTANT definitions: Edges.
            Leader  \* MV CONSTANT definitions: Leader.
CONSTRAINT  constr_1633116534008313000   \* CONSTRAINT definition.
SPECIFICATION Spec                       \* SPECIFICATION definition.
CHECK_DEADLOCK FALSE                     \* CHECK_DEADLOCK definition.
INVARIANT      TypeOK, DT1Inv             \* INVARIANT definitions.
PROPERTY       CountersConsistent         \* PROPERTY definitions.
\* MV CONSTANT declarations
CONSTANTS
    L = 3,                                \* The number of nodes in the system.
    P1 = 0,                               \* The first process ID.
    P2 = 1,                               \* The second process ID.
    P3 = 2                             \* The third process ID.
\* MV CONSTANT definitions: Processes
CONSTANT Procs <- const_163311653400831000
\* MV CONSTANT definitions: Edges
CONSTANT Edges <- const_1633116534008311000
\* MV CONSTANT definitions: Leader
CONSTANT Leader <- const_1633116534008312000
\* CONSTRAINT definition
CONSTRAINT constr_1633116534008313000
    \* The leader process must be a valid node.
    Leader \in Procs
\* SPECIFICATION definition
SPECIFICATION Spec
    \* A distributed tree with a leader node.
    LENGTH(Procs) = L
    Edges \subseteq DOMAIN Procs
    FORALL i,j: 0 <= i < j < L -> (i,j) \in Edges
\* CHECK_DEADLOCK definition
CHECK_DEADLOCK FALSE
\* INVARIANT definitions.
INVARIANT TypeOK
INVARIANT DT1Inv
    \* The leader process must be a valid node.
    Leader \in Procs
FORALL i: 0 <= i < L -> (i,Leader) \in Edges
\* PROPERTY definitions.
PROPERTY CountersConsistent
    \* All nodes have the same counter value.
    FORALL i: 0 <= i < L -> Procs[i].Counter = Procs[(i+1)%L].Counter
PROPERTY TreeWithRoot
    \* The tree is a valid binary search tree with respect to the leader node.
    FORALL n,m: 0 <= n < m < L -> (n,m) \in Edges OR (m,n) \in Edges
\* StableUpEdge
PROPERTY StableUpEdge
    \* The edge from a child to its parent is stable.
    FORALL i,j: 0 <= i < j < L -> (i,j) \in Edges -> Procs[i].Counter = Procs[(j+1)%L].Counter
=============================================================================
====