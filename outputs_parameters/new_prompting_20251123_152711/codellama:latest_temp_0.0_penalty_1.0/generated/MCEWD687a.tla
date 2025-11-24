---- MODULE MCEWD687a ----
------------------------------ MODEL DISTRIBUTED TREES --------------------
(******************************)
(* A distributed tree with a leader. *)
(********************************)
CONSTANTS   L, P1, P2, \* MV CONSTANT declarations @modelParameterConstants *\)
    P3                  (MV CONSTANT definitions Procs)
\*\/ )
(\/\* MV CONSTANT definitions *)
(*******************************)
CONSTANTS   Edges <- const_1633116534008311000, \* CONSTANT definition *\)
    Leader <- const_1633116534008312000 (\*\/ ) (CONSTRAINT definiti *)
*******************************)
(\/\* SPECIFICATION definitio *)
SPECIFICATIO *\)   Spec                          (* INVARIANT definition  \*)
    TypeOK, DT1Inv               ; (\*\/ ) (PROPERTY definiti     *)
******************************)
(\/\* PROPERTIES definitions      **/)
CountersConsistent , TreeWithRoot *\)   StableUpEdge          (* Generated on Fri Oct 01 12:36:49 PDT 2021
====