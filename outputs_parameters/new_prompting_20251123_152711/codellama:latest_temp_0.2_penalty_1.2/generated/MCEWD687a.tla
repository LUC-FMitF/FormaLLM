---- MODULE MCEWD687a ----

(**************************************************************************)
(* Multi-Value (MV) CONSTANT declarations                                *)
CONSTANTS   L = 3,      \* The number of processes.
            P1 = 0,     \* Process 1's identifier.
            P2 = 1,     \* Process 2's identifier.
            P3 = 2;     \* Process 3's identifier.
(**************************************************************************)
(* MV CONSTANT definitions                                               *)
CONSTANT
    Procs <- const_1633116534008310000,   \* The set of all processes.
            Edges <- const_1633116534008311000,  \* The set of all edges in the graph.
            Leader <- const_1633116534008312000;   \* The leader process for each edge.
(**************************************************************************)
(* CONSTRAINT definition                                                *)
CONSTRAINT
    constr_1633116534008313000,  \* TypeOK: All values in the graph are of type L.
    DT1Inv;   \* DT1Inv: The leader process for each edge is a valid process identifier.
(**************************************************************************)
(* SPECIFICATION definition                                       *)
SPECIFICATION
    Spec,  \* The specification of the system.
CHECK_DEADLOCK   FALSE;  \* Whether to check for deadlocks or not.
(**************************************************************************)
(* INVARIANT definitions                                           *)
INVARIANT
    TypeOK,     \* All values in the graph are of type L.
    DT1Inv;      \* The leader process for each edge is a valid process identifier.
(**************************************************************************)
(* PROPERTY definition                                              *)
PROPERTIES   CountersConsistent,  \* Whether or not the counters are consistent.
            TreeWithRoot,    \* Whether or not there exists a tree with root P1.
            StableUpEdge;     \* Whether or not all up edges are stable.
(**************************************************************************)
(* Generated on Fri Oct 01 12:28:54 PDT 2021
====