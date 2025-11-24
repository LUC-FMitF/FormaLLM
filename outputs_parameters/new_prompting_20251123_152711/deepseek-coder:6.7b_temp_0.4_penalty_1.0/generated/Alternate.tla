---- MODULE AlternatingActions 
------------------------------ MODULE AlternatingActions 
(**************************************************************************)
(* This specifies a system that alternately performs two actions, which   *)
(* for now I will call A_0 and A_1.  It uses a variable v whose value      *)
(* alternates between 0 and 1, performing an A_0 action when v changes     *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.               *)
(* *)
(* We let the variable x to represent the part of the state that is        *)
(* changed by the A_0 and A_1 actions.  We introduce two constant           *)
(* operators XInit and XAct, where XInit(x) is assumed to assert that x     *)
(* has a correct initial value, and XAct(i, xInit, xNext) is assumed to     *)
(* assert that changing the value of x from xInit to xNext represent an    *)
(* A_i action, for i=0, 1.                                                  *)
(**************************************************************************)

CONSTANTS 
XInit(x) == (x = EmptySet)
XAct(i, xInit, xNext) == (i = 0 /\ xNext = xInit \/ i = 1 /\ xNext = Not xInit)

VARIABLES 
v == [0, 1]
x == {...}

ASSUME 
\* v changes from 0 to 1 or from 1 to 0
v' == (v = 0 /\ v' = 1 \/ v = 1 /\ v' = 0)

\* x changes correctly
EXISTS xInit, xNext : XInit(xInit) /\ XAct(v, xInit, xNext) /\ xNext = x

\* v' is correct
v' == (v = 0 /\ v' = 1 \/ v = 1 /\ v' = 0)

=============================================================================
====

TLC Configuration:
CONSTANTS 
XInit(x) == (x = EmptySet)
XAct(i, xInit, xNext) == (i = 0 /\ xNext = xInit \/ i = 1 /\ xNext = Not xInit)

SPECIFICATION 
\* v changes from 0 to 1 or from 1 to 0
v' == (v = 0 /\ v' = 1 \/ v = 1 /\ v' = 0)

INVARIANTS 
XInit(x) /\ v' == (v = 0 /\ v' = 1 \/ v = 1 /\ v' = 0)
=============================================================================
====

The TLC configuration specifies the constants and the specification for TLC. The specification states that the variable v changes from 0 to 1 or from 1 to 0. The invariants ensure that the variable x changes correctly and that v' is correct.
====