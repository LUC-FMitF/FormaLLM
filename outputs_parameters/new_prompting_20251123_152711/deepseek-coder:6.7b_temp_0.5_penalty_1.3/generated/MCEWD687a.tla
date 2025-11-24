---- MODULE Lamport  ----
(**************************************************************************)
(* MV CONSTANT declarations@modelParameterConstants                       *)
(**************************************************************************)
LAMPORT_CONSTANTS L = L, P1 = P1, P2 = P2, P3 = P3

\* MV CONSTANT definitions Procs                                      *)
PROCEDURES 
    Procs <- LamportProcedures

\* CONSTANT definitions @modelParameterConstants:1Edges                *)
CONSTANTS 
    Edges <- const_1633116534008311000

\* CONSTANT definitions @modelParameterConstants:2Leader                *)
CONSTANTS 
    Leader <- const_1633116534008312000

\* CONSTRAINT definition                                                 *)
CONSTRAINTS 
    constr_1633116534008313000

\* SPECIFICATION definition                                              *)
SPECIFICATION Spec

CHECK_DEADLOCK FALSE

\* INVARIANT definition                                                  *)
INVARIANTS 
    TypeOK, DT1Inv

\* PROPERTY definition                                                   *)
PROPERTIES 
    DT2

\* PROPERTIES definitions                                                *)
PROPERTIES  
    CountersConsistent, TreeWithRoot, StableUpEdge

(**************************************************************************)
(* Generated on Fri Oct 01 12:28:54 PDT 2021 by lamport                    *)
(**************************************************************************)
====