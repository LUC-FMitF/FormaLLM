---- MODULE EnvironmentController ----
CONSTANTS
    N = 3         -- Number of processes
    T = 1         -- Timeout interval for all delta(p)(q)
    d0 = 2        -- Default time-out interval for all delta(p)(q)
    SendPoint = 2 
    PredictPoint = 3 
    DELTA = 1     -- Constraint of message delay in partial synchrony
    PHI = 1       -- Estimated upper bound of how long a process has not taken a transition. Used to filter out executions that violate the constraint of relative speeds of different processes in partial synchronoy.
INVARIANTS 
    TypeOK        -- A type invariant for your specification
====