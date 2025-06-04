----------------------- MODULE EnvironmentController -----------------------

EXTENDS Integers, TLC

CONSTANT
N,
T,
d0,
SendPoint,
PredictPoint,
DELTA,
PHI

ASSUME  /\ 0 < PredictPoint /\ 0 < SendPoint
/\ PredictPoint % SendPoint # 0 /\ SendPoint % PredictPoint # 0

Proc == 1..N

VARIABLES
inTransit, inDelivery,
suspected, delta, fromLastHeard,
localClock, outgoingMessages,

procPause,
moved,
failed,
F

Messages == [ from : Proc, to : Proc, type : { "alive" } ]

Boxes == [ content : Messages, age : Int ]

K == ((SendPoint * PredictPoint * PHI) \div DELTA) + 1
maxAge == K * (SendPoint * PredictPoint * PHI)
maxDelta == maxAge

CommChan == INSTANCE Age_Channel

Detector == INSTANCE EPFailureDetector

vars == << inTransit, inDelivery,
suspected, delta, fromLastHeard, localClock, outgoingMessages,
procPause, moved, failed, F >>

chanVars == << inTransit, inDelivery >>

procVars == << suspected, delta, fromLastHeard, localClock, outgoingMessages >>

envVars == << procPause, moved, failed, F >>

Actions == { "NO", "INIT", "SEND", "RECEIVE", "PREDICT", "CRASH" }

Init ==
/\ CommChan!Init
/\ Detector!Init
/\ procPause = [ i \in Proc |-> 0 ]
/\ moved = [ i \in Proc |-> "INIT" ]
/\ failed = [ i \in Proc |-> FALSE ]
/\ F = 0

Crash ==
\E i \in Proc :
/\ failed[i] = FALSE
/\ F < T
/\ failed' = [ failed EXCEPT ![i] = TRUE ]
/\ F' = F + 1
/\ moved' = [ moved EXCEPT ![i] = "CRASH" ]
/\ procPause' = [ procPause EXCEPT ![i] = -1 ]
/\ UNCHANGED chanVars
/\ UNCHANGED procVars

SomeLocallyTicked ==
\E p \in Proc : moved[p] # "CRASH" /\ moved[p] # "NO"

EnvTick ==
/\ SomeLocallyTicked
/\ CommChan!AttainAge
/\ moved' = [ i \in Proc |-> "NO" ]
/\ procPause' = [ i \in Proc |-> IF failed[i] = FALSE
THEN procPause[i] + 1
ELSE -1 ]
/\ UNCHANGED << failed, F >>
/\ UNCHANGED procVars

OnlyMessagesForCorrectProcesses(msgs) ==  { m \in msgs : failed[m.to] = FALSE }

ProcTick ==
\E i \in Proc :
\/ /\ failed[i] = TRUE

/\ UNCHANGED envVars
/\ CommChan!Deliver(i)
/\ UNCHANGED procVars
\/ /\ failed[i] = FALSE
/\ moved[i] = "NO"
/\ procPause' = [ procPause EXCEPT ![i] = 0 ]
/\ UNCHANGED << failed, F >>
/\ \/ /\ moved' = [ moved EXCEPT ![i] = "PREDICT" ]
/\ Detector!Predict(i)
/\ UNCHANGED chanVars
\/ /\ moved' = [ moved EXCEPT ![i] = "SEND" ]
/\ Detector!SendAlive(i)
/\ CommChan!Pickup(OnlyMessagesForCorrectProcesses(outgoingMessages'[i]))
\/ /\ moved' = [ moved EXCEPT ![i] = "RECEIVE" ]
/\ CommChan!Deliver(i)
/\ Detector!Receive(i, inDelivery')

PHIConstraint ==
\A i \in Proc : (failed'[i] = FALSE => procPause'[i] <= PHI)

PHIConstraint1 ==
\A i \in Proc : (failed'[i] = TRUE \/ procPause'[i] <= PHI)

DELTAConstraint ==
\A i \in Proc : /\ ((failed'[i] = FALSE /\ moved'[i] = "RECEIVE")
=> ( \A m \in inTransit' : \/ m.content.to # i
\/ m.age <= DELTA ))

Next ==
/\ \/ Crash
\/ EnvTick
\/ ProcTick
/\ DELTAConstraint
/\ PHIConstraint

Spec ==
/\ Init
/\ [][ Next ]_vars
/\ WF_vars( /\ \/ EnvTick
\/ ProcTick
/\ DELTAConstraint
/\ PHIConstraint )

TypeOK ==
/\ CommChan!TypeOK
/\ Detector!TypeOK
/\ procPause \in [ Proc -> { -1 } \cup 0..PHI ]
/\ \A i \in Proc : failed[i] = TRUE <=> procPause[i] = -1
/\ failed \in [ Proc -> BOOLEAN ]
/\ moved \in [ Proc -> Actions]
/\ F \in 0..T
/\ \A i, j \in Proc : 0 <= delta[i][j] /\ delta[i][j] <= maxDelta
/\ \A box \in inTransit : 0 <= box.age /\ box.age <= maxAge
/\ \A i, j \in Proc : fromLastHeard[i][j] <= maxAge

StrongCompleteness ==
<>[] ( \A j \in Proc : failed[j] = TRUE => (\A i \in Proc : \/ failed[i] = TRUE
\/ j \in suspected[i] ) )

EventuallyStrongAccuracy ==
<>[] ( \A i, j \in Proc : (failed[i] = FALSE /\ failed[j] = FALSE)
=> j \notin suspected[i] )

=============================================================================
