---- MODULE MCEWD687a ----

(**************************************************************************)
(* Multi-Value Constant declarations                                      *)
CONSTANTS
    L = L               \* The set of nodes.
    P1 = P1             \* Process 1's ID.
    P2 = P2             \* Process 2's ID.
    P3 = P3             \* Process 3's ID.
(**************************************************************************)
(* MV CONSTANT definitions                                                *)
CONSTANT
    Procs <- const_1633116534008310000 \* The set of all processes.
(**************************************************************************)
(* CONSTANT definitions                                                   *)
CONSTANT
    Edges <- const_1633116534008311000 \* The set of all edges.
CONSTANT
    Leader <- const_1633116534008312000 \* The leader node.
(**************************************************************************)
(* CONSTRAINT definition                                                  *)
CONSTRAINT
    constr_1633116534008313000 \* The constraint on the number of edges.
(**************************************************************************)
(* SPECIFICATION definition                                            *)
SPECIFICATION
    Spec                             \* The specification for the model.
CHECK_DEADLOCK
    FALSE                            \* Whether to check for deadlocks or not.
(**************************************************************************)
(* INVARIANT definition                                               *)
INVARIANT
    TypeOK                           \* The type-checking invariant.
    DT1Inv                            \* The first dynamic transition invariant.
(**************************************************************************)
(* PROPERTY definition                                                  *)
PROPERTY
    DT2                               \* The second dynamic transition property.
PROPERTIES
    CountersConsistent                          \* Whether the counters are consistent or not.
    TreeWithRoot                             \* Whether the tree with the root node is correct or not.
    StableUpEdge                            \* Whether the stable up edge invariant is satisfied or not.
(**************************************************************************)
(* Generated on Fri Oct 01 12:28:54 PDT 2021
====