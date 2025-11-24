---- MODULE EnvironmentController ----
CONSTANTS N T d0 SendPoint PredictPoint DELTA PHI INITIALIZED FAILED CRASHED NO RECEIVE SEND MOVED PROCPAUSE PAUSED
VARIABLES procPause[N] moved'[N][T+1] failed'[N] inTransit'[d0*DELTA*(2^MAX_FAILURE)] outgoingMessages[N][SendPoint-PredictPoint]*(NO/ALIVE) maxAge DELTAConstranti PHIConstraint
INITIALIZATION INITIALIZE N T d0 SendPoint PredictPoint FAILED CRASHED NO RECEIVE SEND MOVED PROCPAUSE PAUSED inTransit' outgoingMessages moved failed procPause
TYPE TypeOK = (proc[i] : 1..N |-> TRUE) & (m.content.to # i -> m.age <= DELTA ) & (paused == FALSE)) /\ ((failed'[i] = TRUE) => ( \A m \in inTransit': /\ m.content.to # i
\/ m.age <= DELTA )))
PROPERTY StrongCompleteness(proc,m): proc FAILED -> exists p : {1..N} |-> true & forall q: {1..N}, (q != i) /\ ((failed'[i] = TRUE ) => ( \A m': inTransit', 0 <= age < DELTA *2^MAX_FAILURE, content.to # p : /\ procPause[p].content == CRASHED))
PROPERTY EventuallyStrongAccuracy(proc): exists t: {1..T} |-> true & forall i: 0 .. N-1 , (moved'[i][t] = NO ) -> !exists j : {1...N}, ((failed'[j]=TRUE) /\ moved'[j][t+1].content == CRASHED))
SPECIFICATION Spec(proc, m): proc FAILED |-> exists p: 0 .. N-1 , (m.to # i & !exists q : {i..N}, ((failed'[q]=TRUE) /\ moved'[p][t+1].content == CRASHED))
====