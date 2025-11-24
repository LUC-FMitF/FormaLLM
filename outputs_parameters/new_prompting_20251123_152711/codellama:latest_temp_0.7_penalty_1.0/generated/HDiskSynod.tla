---- MODULE HDiskSynod ----

CONSTANTS
  Balance,
  Input,
  NotAnInput,
  Output
VARIABLES
  bal,
  inp,
  out
INIT
  /\ bal = 0
  /\ inp = NotAnInput
  /\ out = NotAnOutput
=============================================================================
====