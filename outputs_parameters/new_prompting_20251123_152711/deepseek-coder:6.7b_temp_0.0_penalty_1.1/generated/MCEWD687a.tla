---- MODULE Lamport  ----
(***************************************************************************)
(* MV CONSTANT declarations                                                 *)
(***************************************************************************)
CONSTANTS   L, P1, P2, P3

\* MV CONSTANT definitions
LOCAL INSTANCE Procs

\* CONSTANT definitions @modelParameterConstants:1Edges
LOCAL INSTANCE Edges

\* CONSTANT definitions @modelParameterConstants:2Leader
LOCAL INSTANCE Leader

\* CONSTRAINT definition @modelParameterContraint:0
LOCAL INSTANCE constr_1633116534008313000

=============================================================================
(* TLC Configuration *)
CONSTANTS   L = L, P1 = P1, P2 = P2, P3 = P3

\* MV CONSTANT definitions
CONSTANT    Procs <- const_1633116534008310000

\* CONSTANT definitions @modelParameterConstants:1Edges
CONSTANT    Edges <- const_1633116534008311000

\* CONSTANT definitions @modelParameterConstants:2Leader
CONSTANT    Leader <- const<｜begin▁of▁sentence｜>312000

\* CONSTRAINT definition @modelParameterContraint:0
CONSTRAINT  constr_1633116534008313000 <- const_1633116534008313000

\* SPECIFICATION definition
SPECIFICATION Spec

CHECK_DEADLOCK FALSE

\* INVARIANT definition
INVARIANT TypeOK, DT1Inv

\* PROPERTY definition
PROPERTY DT2

PROPERTIES CountersConsistent, TreeWithRoot (* StableUpEdge *)

\* Generated on Fri Oct 01 12:28:54 PDT 2021
=============================================================================