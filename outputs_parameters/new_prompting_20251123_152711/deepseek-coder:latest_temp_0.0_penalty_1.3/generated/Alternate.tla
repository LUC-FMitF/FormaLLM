---- MODULE Alternate --------

(***************************************************************************)
(* This specifies a system that alternately performs two actions, which     *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value       *)
(* alternates between 0 and 1, performing an A_0 action when v changes      *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.               *)
(* We let the variable x to represent the part of the state that is         *)
(* changed by the A_0 and A_1 actions.  We introduce two constant           *)
(* operators XInit and XAct, where XInit(x) is assumed to assert that x     *)
(* has a correct initial value, and XAct(i, xInit, xNext) is assumed to     *)
(* assert that changing the value of x from xInit to xNext represent an     *)
(* A_i action, for i=0, 1.                                                  *)
(***************************************************************************)

CONSTANTS
  XInit(x)  --  x has a correct initial value
  XAct(i, xInit, xNext)  --  changing the value of x from xInit to xNext represent an A_i action, for i=0, 1

SPECIFICATION Spec

INVARIANTS
  XInit(x)  /\ XAct(i, xInit, xNext)

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Actions

A_0  --  Perform action A_0
A_1  --  Perform action A_1

XInit(x)  --  Assert that x has a correct initial value

XAct(i, xInit, xNext)  --  Assert that changing the value of x from xInit to xNext represent an A_i action, for i=0, 1

Spec  --  Initialize state with XInit(x) and transition with XAct(i, xInit, xNext)

THEOREM Spec 
  --  [](XInit(x)  /\ XAct(i, xInit, xNext))
=============================================================================
====