---- MODULE MCEWD687a ----

(***************************************************************************)
(* MV CONSTANT declarations                                                  *)
(***************************************************************************)
CONSTANTS   L, P1, P2, P3

\* MV CONSTANT definitions
VARIABLES
    Procs <- const_1633116534008310000
    
\* CONSTANT definitions
CONSTANTS
    Edges  <- const_1633116534008311000
    Leader <- const_1633116534008312000
    
\* CONSTRAINT definition
CONSTRAINTS
    DT1Inv == P1 \in Edges /\ P2 \in Edges /\ P3 \in Edges

\* SPECIFICATION definition
SPECIFIES Spec

CHECK_DEADLOCK FALSE

\* INVARIANT definition
INVARIANTS TypeOK, DT1Inv

\* PROPERTY definition
PROPERTIES  DT2

PROPERTIES  
    CountersConsistent,
    TreeWithRoot,
    StableUpEdge

\* Generated on Fri Oct 01 12:28<｜begin▁of▁sentence｜>s PDT 2021 by lamport
=============================================================================
====