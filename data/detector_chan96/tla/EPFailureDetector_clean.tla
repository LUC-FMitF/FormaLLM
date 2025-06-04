------------------------- MODULE EPFailureDetector -------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
Proc,
d0,
SendPoint,
PredictPoint,
Messages

ASSUME  /\ 0 < PredictPoint /\ 0 < SendPoint
/\ PredictPoint % SendPoint # 0 /\ SendPoint % PredictPoint # 0

VARIABLES suspected, delta, fromLastHeard, localClock, outgoingMessages

vars == << suspected, delta, fromLastHeard, localClock, outgoingMessages >>

NULL == -1

MakeAliveMsgsForAll(snder) == { [ from |-> snder, to |-> rcver, type |-> "alive" ] :
rcver \in Proc }

Init ==
/\ suspected = [ i \in Proc |-> {} ]
/\ delta = [ i \in Proc |-> [ j \in Proc |-> d0 ] ]
/\ fromLastHeard = [ i \in Proc |-> [ j \in Proc |-> 0 ] ]
/\ localClock = [ i \in Proc |-> 0 ]
/\ outgoingMessages = [ i \in Proc |-> {} ]

LocallyTick(i) ==
localClock' = [ localClock EXCEPT ![i] =
IF /\ \A j \in Proc : delta[i][j] < localClock[i]
/\ SendPoint < localClock[i]
/\ PredictPoint < localClock[i]
THEN 0
ELSE localClock[i] + 1 ]

SendAlive(i) ==
/\ localClock[i] % PredictPoint # 0
/\ localClock[i] % SendPoint = 0
/\ LocallyTick(i)
/\ outgoingMessages' = [ outgoingMessages EXCEPT ![i] = MakeAliveMsgsForAll(i)]
/\ fromLastHeard' = [ fromLastHeard EXCEPT ![i] =
[ j \in Proc |-> IF fromLastHeard[i][j] <= delta[i][j]
THEN fromLastHeard[i][j]  + 1
ELSE fromLastHeard[i][j] ] ]
/\ UNCHANGED << suspected, delta >>

Receive(i, incomingMessages) ==
/\ \/ /\ localClock[i] % PredictPoint = 0
/\ localClock[i] % SendPoint = 0
\/ /\ localClock[i] % PredictPoint # 0
/\ localClock[i] % SendPoint # 0
/\ LocallyTick(i)
/\ fromLastHeard' = [ fromLastHeard EXCEPT ![i] =
[ j \in Proc |-> IF \E m \in incomingMessages : m.from = j
THEN 0
ELSE IF j \notin suspected[i]
THEN IF fromLastHeard[i][j] <= delta[i][j]
THEN fromLastHeard[i][j] + 1
ELSE fromLastHeard[i][j]
ELSE fromLastHeard[i][j] ] ]
/\ delta' = [ delta EXCEPT ![i] = [ j \in Proc |-> IF /\ j \in suspected[i]
/\ \E m \in incomingMessages : m.from = j
THEN delta[i][j] + 1
ELSE delta[i][j] ] ]
/\ suspected' = [ suspected EXCEPT ![i] = suspected[i] \ { j \in Proc : (\E msg \in incomingMessages : msg.from = j) } ]
/\ UNCHANGED outgoingMessages

Predict(i) ==
/\ localClock[i] % PredictPoint = 0
/\ localClock[i] % SendPoint # 0
/\ LocallyTick(i)
/\ suspected' = [ suspected EXCEPT ![i] = suspected[i] \cup { j \in Proc : fromLastHeard[i][j] > delta[i][j] } ]
/\ UNCHANGED outgoingMessages
/\ fromLastHeard' = [ fromLastHeard EXCEPT ![i] = [ j \in Proc |-> IF fromLastHeard[i][j] <= delta[i][j]
THEN fromLastHeard[i][j] + 1
ELSE fromLastHeard[i][j] ] ]
/\ UNCHANGED << delta >>

TypeOK ==
/\ fromLastHeard \in [ Proc -> [ Proc -> Int ] ]
/\ \A p, q \in Proc : fromLastHeard[p][q] \in Int
/\ delta \in [ Proc -> [ Proc -> Int ] ]
/\ suspected \in [ Proc -> SUBSET Proc ]
/\ outgoingMessages  \in [ Proc -> SUBSET Messages ]

=============================================================================
