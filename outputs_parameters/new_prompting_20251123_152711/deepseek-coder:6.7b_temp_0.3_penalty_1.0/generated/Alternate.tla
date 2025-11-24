---- MODULE Alternate ----

(***************************************************************************)
(* This specifies a system that alternately performs two actions, which     *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value       *)
(* alternates between 0 and 1, performing an A_0 action when v changes      *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.               *)
(* *)
(* We let the variable x to represent the part of the state that is         *)
(* changed by the A_0 and A_1 actions.  We introduce two constant           *)
(* operators XInit and XAct, where XInit(x) is assumed to assert that x     *)
(* has a correct initial value, and XAct(i, xInit, xNext) is assumed to     *)
(* assert that changing the value of x from xInit to xNext represent an     *)
(* A_i action, for i=0, 1.                                                  *)
(* *)
(* A philosophically correct spec would actually be                         *)
(* *)
(* \EE v  : Spec                                                          *)
(* *)
(* which is the specification Spec with v hidden.  However, engineers are   *)
(* interested in what works, not what is philosophically correct, so we     *)
(* don't worry about this.                                                  *)
(* *)
(***************************************************************************)

CONSTANTS
  A_0 = {0}
  A_1 = {1}

VARIABLES
  v, x

ASSUME
  XInit(x) == TRUE
  XAct(0, x, x') == (x' = x + 1)
  XAct(1, x, x') == (x' = x - 1)

NEXT(v) == IF v IN A_0 THEN A_1 ELSE A_0

SPECIFICATION
  [v \in A_0] XInit(x) /\ XAct(0, x, x')
  [v \in A_1] XInit(x) /\ XAct(1, x, x')

INVARIANTS
  TypeOK

TLC Configuration:
CONSTANTS
  A_0 = {0}
  A_1 = {1}
SPECIFICATION
  [v \in A_0] XInit(x) /\ XAct(0, x, x')
  [v \in A_1] XInit(x) /\ XAct(1, x, x')
INVARIANTS
  TypeOK
=============================================================================
====
### Instruction:<｜begin▁of▁sentence｜>
====