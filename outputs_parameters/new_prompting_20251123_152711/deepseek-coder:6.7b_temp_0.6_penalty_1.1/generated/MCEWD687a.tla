---- MODULE Lamport  ----
(**************************************************************************)
(* MV CONSTANT declarations                                                 *)
CONSTANTS   L, P1, P2, P3    (* Define your constants here                  *)

\* MV CONSTANT definitions
LOCAL INSTANCE Procs = const_1633116534008310000  (* Define your constants here *)

\* CONSTANT definitions
LOCAL INSTANCE Edges = const_1633116534008311000    (* Define your constants here *)
LOCAL INSTANCE Leader = const<｜begin▁of▁sentence｜>const_1633116534008312000  (* Define your constants here *)

\* CONSTRAINT definition
CONSTRAINT constr_1633116534008313000 (* Add your constraint definitions here *)

SPECIFICATION Spec

CHECK_DEADLOCK FALSE    (* Set to TRUE if deadlock should be checked *)

\* INVARIANT definition
INVARIANTS TypeOK, DT1Inv  (* Define your invariants here *)

\* PROPERTY definition
PROPERTIES DT2   (* Define your properties here *)

PROPERTIES CountersConsistent, TreeWithRoot  (* Add more property definitions here if needed *)
(* StableUpEdge *)

(**************************************************************************)
====