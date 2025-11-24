---- MODULE Lamport  ----
(***************************************************************************)
(* MV CONSTANT declarations                                                 *)
CONSTANTS
    L = L, (* Replace with actual value or expression *)
    P1 = P1, (* Replace with actual value or expression *)
    P2 = P2, (* Replace with actual value or expression *)
    P3 = P3  (* Replace with actual value or expression *)

(* MV CONSTANT definitions                                                  *)
CONSTANTS
    Procs <- const_1633116534008310000, (* Replace with actual value or expression *)
    Edges <- const_1633116534008311000, (* Replace with actual value or expression *)
    Leader <- const<｜begin▁of▁sentence｜>const_1633116534008312000  (* Replace with actual value or expression *)

(* CONSTRAINT definition                                                    *)
CONSTRAINTS
    constr_1633116534008313000 (* Replace with actual constraint *)

SPECIFICATION Spec

CHECK_DEADLOCK FALSE

(* INVARIANT definition                                                   *)
INVARIANTS
    TypeOK,
    DT1Inv

(* PROPERTY definition                                                    *)
PROPERTIES
    CountersConsistent,
    TreeWithRoot,
    (* StableUpEdge *)

(* Generated on Fri Oct 01 12:28:54 PDT 2021 *)
=============================================================================