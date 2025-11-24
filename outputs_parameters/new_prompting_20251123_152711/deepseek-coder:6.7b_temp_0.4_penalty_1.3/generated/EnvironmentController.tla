---- MODULE EnvironmentController ----
\* Module Definition *
MODULE EPFailureDetector
EXTENDS Age_Channel, EnvironmentController
CONSTANTS N = 3, T = 1, d0 = 2, SendPoint = 2, PredictPoint = 3, DELTA = 1, PHI = 1
VARIABLES moved[N], failed[N]
ASSUME \A i : {1..N} : (moved'[i] = NO) -> ((failed'[i] = TRUE) => (\EX m : Message : 
    (((m.content.to # i) OR (m.age < DELTA)))))
DEFINE
    Spec == {EPFailureDetector} /\ EnvironmentControllerSpec
====