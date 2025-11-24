---- MODULE Alternate --------

(***************************************************************************)
(* This specifies a system that alternately performs two actions, which     *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value       *)
(* alternates between 0 and 1, performing an A_0 action when v changes      *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.               *)
(***************************************************************************)

CONSTANTS A_0, A_1, v, x

VARIABLES xInit, xNext

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

XInit(x) == 
  IF x ∈ {0, 1}
  THEN xInit ∈ {0, 1}
  ELSE FALSE

XAct(i, xInit, xNext) ==
  IF i ∈ {0, 1}
  THEN IF xInit ∈ {0, 1}
       THEN x ← xInit
       ELSE x ← xNext
  ELSE FALSE

A_0(v) ==
  IF v ∈ {0, 1}
  THEN IF XInit(x)
       THEN XAct(0, xInit, xNext)
       ELSE XAct(1, xInit, xNext)
  ELSE FALSE

A_1(v) ==
  IF v ∈ {0, 1}
  THEN IF XInit(x)
       THEN XAct(0, xInit, xNext)
       ELSE XAct(1, xInit, xNext)
  ELSE FALSE

Spec 
  A_0(v) 
  /\ A_1(v)

Theorems Spec 
  A_0(v) 
  /\ A_1(v)

=============================================================================
====