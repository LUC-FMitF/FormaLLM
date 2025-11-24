---- MODULE Alternate ----

(***************************************************************************)
(* This specifies a system that alternately performs two actions, which     *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value       *)
(* alternates between 0 and 1, performing an A_0 action when v changes      *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.               *)
*)
(* We let the variable x to represent the part of the state that is         *)
(* changed by the A_0 and A_1 actions.  We introduce two constant           *)
(* operators XInit and XAct, where XInit(x) is assumed to assert that x     *)
(* has a correct initial value, and XAct(i, xInit, xNext) is assumed to     *)
(* assert that changing the value of x from xInit to xNext represent an     *)
(* A_i action, for i=0, 1.                                                  *)
***************************************************************************)

CONSTANTS
    XInit == <<>>, (* Assumes a correct initial value for x *)
    XAct(i, xInit, xNext) == [x |-> IF i = 0 THEN xInit ELSE xNext], (* Asserts that changing the value of x from xInit to xNext represents an A_i action *)
    v == 1; (* Initial value of variable v *)

VARIABLES
    x == XInit(x); (* Initial value of variable x *)

OPERATIONS
    NextState() == IF v = 0 THEN [v |-> 1, x |-> XAct(0, x, XNext())]
                  ELSE [v |-> 0, x |-> XAct(1, x, XNext())]; (* The next state operation *)

\* The set of all possible states *)
State == UNION {[s |-> NextState()]: s \in State} /\ [x |-> XInit(x)],

SPECIFICATION Spec == []v = 0 -> AFG([]v = 1) /\ GF([]v = 0), (* The specification *)

INVARIANTS 
    TypeOK == TRUE; (* Assume all invariants hold *)

TLC Configuration:
CONSTANTS 
    XInit == <<>>, 
    XAct(i, xInit, xNext) == [x |-> IF i = 0 THEN xInit ELSE xNext], 
    v == 1; 
SPECIFICATION Spec == []v = 0 -> AFG([]v = 1) /\ GF([]v = 0),
INVARIANTS TypeOK == TRUE;
=============================================================================
====