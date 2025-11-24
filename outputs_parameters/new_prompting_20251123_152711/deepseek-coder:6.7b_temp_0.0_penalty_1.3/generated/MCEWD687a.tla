---- MODULE Lamport  ----
(****************************************************************************)
(* Modification History                                                   *)
(* Created Fri Oct 01 12:28:54 PDT 2021 by lamport                          *)
(*****************************************************************************)
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
  
\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS 
    L = \* Number of nodes *\/
    P1 = \* Processes *\/
    P2 = \* Leader election process *\/
    P3 = \* Updating edge information process *\/
  
\* MV CONSTANT definitions Procs
CONSTANTS 
    Procs <- const_1633116534008310000 /\* Processes definition *\/
    
\* CONSTANT definitions @modelParameterConstants:1Edges
CONSTANTS 
    Edges <- const_1633116534008311000 /\* Edge information definition *\/
  
\* CONSTANT definitions @modelParameterConstants:2Leader
CONSTANTS 
    Leader <- const<｜begin▁of▁sentence｜>const_1633116534008312000 /\* Leader election process definition *\/
    
\* CONSTRAINT definition @modelParameterContraint:0
CONSTANT 
    EdgesConstraints <- const_1633116534008313000 /\* Edge constraints definition *\/
  
SPECIFICATION Spec
CHECK_DEADLOCK FALSE
INVARIANT TypeOK DT1Inv 
PROPERTY DT2 CountersConsistent TreeWithRoot StableUpEdge
=============================================================================