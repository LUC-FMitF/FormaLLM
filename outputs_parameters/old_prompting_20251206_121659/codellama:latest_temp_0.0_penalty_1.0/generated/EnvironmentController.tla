---- MODULE EnvironmentController ----
EXTENDS
  Age_Channel,
  EPFailureDetector
CONSTANTS
  N = 3
  T = 1
  d0 = 2
  SendPoint = 2
  PredictPoint = 3
  DELTA = 1
  PHI = 1
VARIABLES
  moved[i \in 1..N] = "NO"
  failed[i \in 1..N] = FALSE
  maxAge = 10
  maxDelta = 10
INIT
  Init
NEXT
  Next
SPEC
  Spec
INVARIANT
  TypeOK
PROPERTY
  StrongCompleteness
  EventuallyStrongAccuracy
====