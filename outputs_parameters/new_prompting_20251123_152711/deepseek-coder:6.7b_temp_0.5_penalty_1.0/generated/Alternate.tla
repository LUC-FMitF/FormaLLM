---- MODULE Alternate ----


CONSTANTS 
  A_0,
  A_1

VARIABLES 
  v,
  x

ASSUME 
  XInit(x) /\ 
  XAct(0, x, new_x) ==> v' = 1 /\ new_x != x
  XAct(1, x, new_x) ==> v' = 0 /\ new_x != x

Next ==
  [] v = 0 /\ v' = 1 /\ XAct(0, x, new_x)
  [] v = 1 /\ v' = 0 /\ XAct(1, x, new_x)

Spec == Init /\ [][Next]_<<x>>

---- END OF MODULE AlternatingActions ----

TLC Configuration:
CONSTANTS 
  A_0 = "A_0",
  A_1 = "A_1"

SPECIFICATION Spec

INVARIANTS 
  "XInit(x)",
  "XAct(0, x, new_x) ==> v' = 1 /\ new_x != x",
  "XAct(1, x, new<｜begin▁of▁sentence｜>) ==> v' = 0 /\ new_x != x"

=============================================================================
====