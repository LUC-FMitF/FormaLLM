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
(* assert that changing the value of x from xInit to xNext represent an    *)
(* A_i action, for i=0, 1.                                                  *)
***************************************************************************)

CONSTANTS
\* Initial values for variables
v == 0 /\ x == EmptySet

VARIABLES
\* Variable v alternates between 0 and 1
Next[v] == IFSELF v = 0 THEN 1 ELSE 0 END

OPERATORS
XInit(x) == EMPTYSET /\ x IN X_NEXT
XAct(i, xInit, xNext) == 
    EXTENSION {<x -> xInit>} UNION {<x -> xNext>} 
    COND (Cardinality[x] = 1) /\ ((i = 0 /\ Next[v] = 1) \/ (i = 1 /\ Next[v] = 0))

INVARIANTS
TypeOK == [v IN {0, 1}] /\ x SUBSET XInit(x)

SPECIFICATION Spec == 
    [] v = 0 -> XAct(0, XInit(x), {<x -> ElemOf(X_NEXT)} UNION ({<x -> EmptySet>} IFSELF Cardinality[x] > 1)) 
    /\ [] v = 1 -> XAct(1, XInit(x), {<x -> ElemOf(X_NEXT)} UNION ({<x -> EmptySet>} IFSELF Cardinality[x] > 1)))

TLC Configuration:
CONSTANTS
\* Initial values for variables
v == 0 /\ x == {}

SPECIFICATION Spec 
    --module=AlternatingActions 
    --disable-extensionality 
    --deadlock-cycle 
=============================================================================
====