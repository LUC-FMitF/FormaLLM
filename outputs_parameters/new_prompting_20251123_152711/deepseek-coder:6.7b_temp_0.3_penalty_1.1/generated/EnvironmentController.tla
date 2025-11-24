---- MODULE EnvironmentController ----
EXTENDS Age_Channel, EPFailureDetector
CONSTANTS
    N = 3, -- Number of processes
    T = 1, -- Timeout interval for all delta(p)(q)
    d0 = 2, 
    SendPoint = 2, 
    PredictPoint = 3, 
    DELTA = 1, 
    PHI = 1
INVARIANTS
    TypeOK = (-- definition of type OK goes here --),
    StrongCompleteness = (-- definition of strong completeness goes here --),
    EventuallyStrongAccuracy = (-- definition of eventually strong accuracy goes here --)
OPERATIONS
    Initialize = (-- initialization operations go here --),
    Tick = (-- tick operation goes here --),
    SendAliveMessage = (-- send alive message operation goes here --),
    ReceiveNewMessages = (-- receive new messages operation goes here --)
DEFINITIONS
    Spec = Initialize \/ Tick /\ SendAliveMessage /\ ReceiveNewMessages
====