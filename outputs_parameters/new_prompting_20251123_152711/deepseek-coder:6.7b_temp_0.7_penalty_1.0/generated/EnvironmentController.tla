---- MODULE EnvironmentController ----
CONSTANTS
  N = 3
  T = 1
  d0 = 2

OPERATORS
  NextState

FUNCTIONS
  Init
    x \in N := d0
  NextState
    x \in N, s \in State := IF x = s[1] THEN (s[2] + 1) MOD N ELSE s[2] + 1 MOD N FI

VARIABLES
  State \in \powerset(N \times \nat)

ASSIGN
  INIT Init
  NEXT NextState[CURRENT]
====