---- MODULE Lamport  ----
(***************************************************************************)
(* Modification History                                                    *)
(* Created Fri Oct 01 12:28:54 PDT 2021 by lamport                          *)
(****************************************************************************)
LOCAL INSTANCE ModelParameters
   CONSTANTS L = L, P1 = P1, P2 = P2, P3 = P3
   
\* MV CONSTANT definitions Procs -----------------------------------------
CONSTANT Procs <- const_1633116534008310000 (* replace with actual value *)
  
\* MV CONSTANT definitions @modelParameterConstants:1Edges ------------------
CONSTANT Edges  <- const_1633116534008311000 (* replace with actual value *)
   
\* MV CONSTANT definitions @modelParameterConstants:2Leader ---------------
CONSTANT Leader <- const<｜begin▁of▁sentence｜>const_1633116534008312000 (* replace with actual value *)
  
(* CONSTRAINT definition@modelParameterContraint:0 *)
\* SPECIFICATION definitions --------------------------------------------------
SPECIFICATION Spec (* Define your specification here. Replace this comment.*)
   
CHECK_DEADLOCK FALSE
    
\* INVARIANT definitions -----------------------------------------------
INVARIANT TypeOK   (* Add actual invariant definition *)
INVARIANT DT1Inv  (* Add actual invariant definition *)
     
(* PROPERTY definitions *)
PROPERTIES CountersConsistent, TreeWithRoot (* Replace with your properties.*)
   
\* Generated on Fri Oct 01 12:28:54 PDT 2021 by lamport                          *)
=============================================================================