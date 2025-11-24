---- MODULE MCEWD687a ----

(**********************************************)
(*                                            *)
(*    This module defines a distributed tree   *)
(*      with leader election and locking.     *)
(*                                            *)
(**********************************************)
CONSTANTS L, P1, P2, P3 \* MV CONSTANT declarations@modelParameterConstants
-------------------------
\* MV CONSTANT definitions Procs
PROCS <- const_1633115984007820000
--------------
\* CONSTANT definitions @modelParameterConstants:1Edges
EDGES <- const_1633115984007821000 \* MV CONSTANT definitions @modelParameterConstants:2Leader
LEADER <- const_1633115984007822000 \* CONSTANT definitions @modelParameterContraints:0 Modification History Created Fri Oct 01 12:28:54 PDT 2021 by lamport
----------------------------- -----
\* SPECIFICATION definition Spec CHECK_DEADLOCK FALSE \* INVARIANT definition TypeOK DT1Inv PROPERTY DT2 Properties CountersConsistent TreeWithRoot StableUpEdge Generated on Fri Oct 01 12:28:54 PDT 2021
====