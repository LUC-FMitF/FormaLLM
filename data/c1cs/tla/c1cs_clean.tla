-------------------------------- MODULE c1cs --------------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANT N, F, T, Values, Bottom

ASSUME 3 * T < N /\ 0 <= F /\ F <= T /\ 0 < N

VARIABLES pc, v, dValue, bcastMsg, rcvdMsg

vars == << pc, v, dValue, bcastMsg, rcvdMsg >>

Proc == 1..N

Location == { "PROPOSE", "DECIDE", "CALL", "CRASH", "DONE" }

makeProposedMsg(v_i, i) == [ type |-> "Proposed", value |-> v_i, sndr |-> i ]
makeDecisionMsg(v_i, i ) == [ type |-> "Decision", value |-> v_i, sndr |-> i ]

PMsg == [ type : {"Proposed"} , value : Values, sndr : Proc ]
DMsg == [ type : {"Decision"}, value : Values, sndr : Proc ]
Msg == PMsg \cup DMsg

Init ==
/\ v \in [ Proc -> Values ]
/\ pc = [ i \in Proc |-> "PROPOSE" ]
/\ dValue = [ i \in Proc |-> Bottom ]
/\ bcastMsg = {}
/\ rcvdMsg = [ i \in Proc |-> {} ]

Crash(i) ==
/\ Cardinality( { p \in Proc : pc[p] # "CRASH" } ) <  F
/\ pc[i] # "CRASH"
/\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
/\ UNCHANGED << dValue, v, bcastMsg, rcvdMsg >>

Receive(i) ==
/\ pc[i] # "CRASH"
/\ \E sndr \in Proc, msg \in Msg:
/\ msg \in bcastMsg
/\ msg \notin rcvdMsg[i]
/\ rcvdMsg' = [ rcvdMsg EXCEPT ![i] = rcvdMsg[i] \cup { msg } ]
/\ UNCHANGED << pc, v, dValue, bcastMsg >>

Propose(i) ==
/\ pc[i] = "PROPOSE"
/\ pc' = [ pc EXCEPT ![i] = "DECIDE" ]
/\ bcastMsg' = bcastMsg \cup { makeProposedMsg(v[i], i) }
/\ UNCHANGED << v, dValue, rcvdMsg >>

Core_T1(i) ==
/\ pc[i] = "DECIDE"
/\ Cardinality({ msg \in rcvdMsg[i] : msg.type = "Proposed" }) >= N - T
/\ IF /\ (\E tV \in Values : \A msg \in rcvdMsg[i] : msg.type = "Proposed" => msg.value = tV)
THEN /\ dValue' = [ dValue EXCEPT ![i] = CHOOSE tV \in Values : (Cardinality({ msg \in rcvdMsg[i] : msg.type = "Proposed" /\ msg.value = tV }) >= N - T) ]
/\ bcastMsg' = bcastMsg \cup { makeDecisionMsg(dValue'[i], i) }
/\ pc' = [ pc EXCEPT ![i] = "DONE" ]
/\ UNCHANGED << v >>
ELSE /\ IF \E tV \in Values : Cardinality({ msg \in rcvdMsg[i] : msg.type = "Proposed" /\ msg.value = tV }) >= N - 2 * T
THEN /\ v' = [ v EXCEPT ![i] = CHOOSE tV \in Values : (Cardinality({ msg \in rcvdMsg[i] : msg.type = "Proposed" /\ msg.value = tV }) >= N - 2 * T) ]
/\ UNCHANGED << dValue, bcastMsg >>
ELSE UNCHANGED << dValue, v, bcastMsg >>
/\ pc' = [ pc EXCEPT ![i] = "CALL" ]
/\ UNCHANGED << rcvdMsg >>

T2(i) ==
/\ pc[i] # "DONE"
/\ pc[i] # "CRASH"
/\ \E msg \in rcvdMsg[i]:
/\ msg.type = "Decision"
/\ dValue' = [ dValue EXCEPT ![i] = msg.value ]
/\ bcastMsg' = bcastMsg \cup { makeDecisionMsg(dValue'[i], i) }
/\ pc' = [ pc EXCEPT ![i] = "DONE" ]
/\ UNCHANGED << v, rcvdMsg >>

DoNothing(i) ==
/\ \/ pc[i] = "CALL"
\/ pc[i] = "DONE"
/\ UNCHANGED vars

Next ==
\E i \in Proc: \/ Crash(i)
\/ Receive(i)
\/ Propose(i)
\/ Core_T1(i)
\/ T2(i)
\/ DoNothing(i)

Spec == Init /\ [][Next]_<< pc, v, dValue, bcastMsg, rcvdMsg >>
/\ WF_vars(\E i \in Proc : \/ Receive(i)
\/ Propose(i)
\/ Core_T1(i)
\/ T2(i))

TypeOK ==
/\ v \in [ Proc -> Values ]
/\ pc \in [ Proc -> Location ]
/\ bcastMsg \in SUBSET (PMsg \cup DMsg)
/\ rcvdMsg \in [ Proc -> SUBSET (PMsg \cup DMsg) ]
/\ dValue \in [ Proc -> { Bottom } \cup Values ]

Validity == \A i \in Proc : ((dValue[i] # Bottom) => (\E j \in Proc : dValue[i] = v[j]))

Agreement ==
/\ \A i, j \in Proc : ((dValue[i] # Bottom /\ dValue[j] # Bottom) => (dValue[i] = dValue[j]))
/\ \A i \in Proc : pc[i] = "CALL" => (\A j \in Proc : pc[j] = "DONE" => v[i] = dValue[j])

WeakAgreement ==
/\ \A i, j \in Proc : ((dValue[i] # Bottom /\ dValue[j] # Bottom) => (dValue[i] = dValue[j]))

Termination == <>(\A i \in Proc : pc[i] = "CRASH" \/ pc[i] = "DONE" \/ pc[i] = "CALL")

IndStrengthens ==
/\ TypeOK

/\ \A msg \in bcastMsg : (msg.type = "Proposed" /\ (pc[msg.sndr] = "PROPOSE" \/ pc[msg.sndr] = "DECIDE"))
=> msg.value = v[msg.sndr]

/\ \A msg1 \in bcastMsg, msg2 \in bcastMsg : (msg1.sndr = msg2.sndr /\ msg1.type = msg2.type)
=> msg1.value = msg2.value

/\ \A msg1 \in bcastMsg, msg2 \in bcastMsg : (msg1.type = "Decision" /\ msg2.type = "Decision")
=> msg1.value = msg2.value

/\ \A msg1 \in bcastMsg : msg1.type = "Decision" => (Cardinality( { msg2 \in bcastMsg : msg2.type = "Proposed" /\ msg1.value = msg2.value} ) >= N - T)

/\ \A i \in Proc : pc[i] = "PROPOSE" => ((\A msg \in bcastMsg : msg.sndr # i) )

/\ \A i \in Proc : dValue[i] = Bottom => (\A msg \in bcastMsg : msg.type = "Decision" => msg.sndr # i)

/\ \A i \in Proc : pc[i] = "DONE" => dValue[i] # Bottom

/\ \A i \in Proc : dValue[i] # Bottom => (\E msg \in bcastMsg : msg.sndr = i /\ msg.type = "Decision" /\ msg.value = dValue[i])

/\ \A i \in Proc : dValue[i] # Bottom => (pc[i] # "PROPOSE" /\ pc[i] # "DECIDE")

/\ \A i \in Proc : (pc[i] = "PROPOSE" \/ pc[i] = "DECIDE") => ((\A msg \in bcastMsg : dValue[i] = Bottom) )

/\ \A i \in Proc: rcvdMsg[i] \subseteq bcastMsg

=============================================================================
