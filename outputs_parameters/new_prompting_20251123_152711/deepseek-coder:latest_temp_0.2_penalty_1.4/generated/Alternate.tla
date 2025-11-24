---- MODULE Alternate --------

(**************************************************************************)
(* A system that alternately performs two actions, A_0 and A_1.  It uses a variable *)
(* v whose value alternates between 0 and 1, performing an A_0 action when v changes *)
(* from 0 to 1, and an A_1 action when v changes from 1 to 0.  We let the variable *)
(* x to represent the part of the state that is changed by the A_0 and A_1 actions. *)
(**************************************************************************)

CONSTANTS XInit, XAct 

VARIABLES v, x

INITIAL 
  v = 0

ACTIONS A_0, A_1
  IF v = 0
  THEN 
    x = 0
    XInit(x)
  ELSE 
    x = 1
    XAct(0, xInit, xNext)

ACTIONS A_1
  IF v = 1
  THEN 
    x = 0
    XInit(x)
  ELSE 
    x = 1
    XAct(1, xNext, x)

SPEC Spec
  A_0(v) 
  A_1(v)

XInit(x) 
  IF x = 0
  THEN 
    XAct(0, xInit, xNext)
  ELSE 
    XAct(1, xNext, x)

XAct(i, xInit, xNext) 
  IF i = 0
  THEN 
    x = xInit
  ELSE 
    x = xNext

XAct(i, xNext, x) 
  IF i = 1
  THEN 
    x = xNext
  ELSE 
    x = x

SPEC Spec
  A_0(v) 
  A_1(v)

THEOREM Spec 
  XInit(x) 
  XAct(i, xInit, xNext)
  XAct(i, xNext, x)

=============================================================================
====