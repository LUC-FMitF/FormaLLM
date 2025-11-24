---- MODULE EnvironmentController ----
\* The number of processes
CONSTANTS N = 3

\* The maximum number of failures
CONSTANTS T = 1

\* The default time-out interval for all delta(p)(q)
CONSTANTS d0 = 2

\* Every correct process sends alive messages to others at every SendPoint ticks of its local clock. 
CONSTANTS SendPoint = 2

\* Every correct process makes predictions about failures at every PredictPoint ticks of its lock clock.
CONSTANTS PredictPoint = 3

\* Assumptions about the constraints in our system.
\* SendPoint # PredictPoint: a process cannot both send messages and receive messages in one transition. 
\* PredictPoint % SendPoint # 0 : the operation Predict cannot subsume the operation Predict and vice versa.
CONSTANTS DELTA = 1, PHI = 1
====