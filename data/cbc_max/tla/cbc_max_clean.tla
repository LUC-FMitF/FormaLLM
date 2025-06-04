---------------------------- MODULE cbc_max ----------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANT N, F, T, Values, Bottom

ASSUME 2 * T < N /\ 0 <= F /\ F <= T /\ 0 < N
ASSUME \A v \in Values: v # Bottom

VARIABLES pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs

vars == << pc, V, v, w, dval, nCrash, sntMsgs, rcvdMsgs >>

Proc == 1..N

Status == { "BCAST1", "PHS1", "PREP","BCAST2", "PHS2", "DONE", "CRASH", "CHOOSE" }

Phs1Msg(v_i, i) == [ type |-> "Phs1", value |-> v_i, sndr |-> i ]
Phs2Msg(v_i, w_i, i) == [ type |-> "Phs2", value |-> v_i, wValue |-> w_i, sndr |-> i ]

Msg1s == [ type: {"Phs1"} , value: Values, sndr: Proc ]
Msg2s == [ type: {"Phs2"}, value: Values, wValue: Values, sndr: Proc ]
Msgs == Msg1s \cup Msg2s

MAX(arr) == CHOOSE maxVal \in Values: /\ (\E p \in Proc: arr[p] = maxVal)
/\ (\A p \in Proc: maxVal >= arr[p])

Init ==
/\ V = [ i \in Proc |-> [ j \in Proc |-> Bottom ] ]
/\ v \in [ Proc -> Values ]
/\ pc = [ i \in Proc |-> "BCAST1" ]
/\ w = [ i \in Proc |-> Bottom ]
/\ dval = [ i \in Proc |-> Bottom ]
/\ nCrash = 0
/\ sntMsgs = {}
/\ rcvdMsgs = [ i \in Proc |-> {} ]

Crash(i) ==
/\ nCrash < F
/\ pc[i] # "CRASH"
/\ nCrash' = nCrash + 1
/\ pc' = [ pc EXCEPT ![i] = "CRASH" ]
/\ UNCHANGED << V, w, dval, v, sntMsgs, rcvdMsgs >>

Receive(i) ==
\E msg \in Msgs :
/\ pc[i] # "CRASH"
/\ msg \in sntMsgs
/\ msg \notin rcvdMsgs[i]
/\ rcvdMsgs' = [ rcvdMsgs EXCEPT ![i] = rcvdMsgs[i] \cup { msg } ]
/\ LET j == msg.sndr
IN V' = [ V EXCEPT ![i][j] = IF \/ /\ pc[i] = "PHS1"
/\ msg.type = "Phs1"
\/ /\ pc[i] = "PHS2"
/\ msg.type = "Phs2"
THEN msg.value
ELSE V[i][j] ]
/\ UNCHANGED << pc, v, w, dval, nCrash, sntMsgs, V >>

BcastPhs1(i) ==
/\ pc[i] = "BCAST1"
/\ pc' = [ pc EXCEPT ![i] = "PHS1" ]
/\ sntMsgs' = sntMsgs \cup { Phs1Msg(v[i], i) }
/\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

Phs1(i) ==
/\ pc[i] = "PHS1"
/\ pc' = [ pc EXCEPT ![i] = "BCAST2" ]
/\ Cardinality({ m \in rcvdMsgs[i]: m.type = "Phs1" }) >= N - T
/\ w' = [ w EXCEPT ![i] = MAX(V[i]) ]
/\ UNCHANGED << v, dval, nCrash, sntMsgs, rcvdMsgs, V >>

BcastPhs2(i) ==
/\ pc[i] = "BCAST2"
/\ pc' = [ pc EXCEPT ![i] = "PHS2" ]
/\ sntMsgs' = sntMsgs \cup { Phs2Msg(v[i], w[i], i) }
/\ UNCHANGED << V, v, w, dval, nCrash, rcvdMsgs >>

Phs2(i) ==
/\ pc[i] = "PHS2"
/\ \/ \E v0 \in Values:
/\ Cardinality( { m \in rcvdMsgs[i]: m.type = "Phs2" /\ m.wValue = v0 } )  >= N - T
/\ dval' = [ dval EXCEPT ![i] = v0 ]
/\ pc' = [ pc EXCEPT ![i] = "DONE" ]
/\ UNCHANGED << v, w, nCrash, sntMsgs, rcvdMsgs, V >>
\/ /\ \A j \in Proc: \E m \in rcvdMsgs[i] : m.type = "Phs2" /\ m.sndr = j
/\ pc' = [ pc EXCEPT ![i] = "CHOOSE"]
/\ UNCHANGED << v, w, nCrash, sntMsgs, dval, rcvdMsgs, V >>

Choose(i) ==
/\ pc[i] = "CHOOSE"
/\ dval' = [ dval EXCEPT ![i] = (CHOOSE tV \in Values: (\E j \in Proc: tV = V[i][j])) ]
/\ pc' = [ pc EXCEPT ![i] = "DONE" ]
/\ UNCHANGED << V, v, w, nCrash, sntMsgs, rcvdMsgs >>

Next == \E i \in Proc: \/ Crash(i)
\/ Receive(i)
\/ BcastPhs1(i)
\/ Phs1(i)
\/ BcastPhs2(i)
\/ Phs2(i)
\/ Choose(i)
\/ /\ \A p \in Proc : pc[p] = "CRASH" \/ pc[p] = "DONE"
/\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
/\ WF_vars(\E i \in Proc: \/ Receive(i)
\/ BcastPhs1(i)
\/ Phs1(i)
\/ BcastPhs2(i)
\/ Phs2(i)
\/ Choose(i))

TypeOK ==
/\ V \in [ Proc -> [ Proc -> { Bottom } \cup Values ] ]
/\ v \in [ Proc -> Values ]
/\ pc \in [ Proc -> Status ]
/\ w \in [ Proc -> { Bottom } \cup Values ]
/\ dval \in [ Proc -> { Bottom } \cup Values ]
/\ nCrash \in 0 .. F
/\ sntMsgs \in SUBSET Msgs
/\ rcvdMsgs \in [ Proc -> SUBSET Msgs ]

Validity == (\A i \in Proc: dval[i] # Bottom => (\E j \in Proc: dval[i] = v[j]))

Agreement == \A i, j \in Proc: (dval[i] # Bottom /\ dval[j] # Bottom) => dval[i] = dval[j]

Termination == <>(\A i \in Proc: pc[i] = "CRASH" \/ pc[i] = "DONE")

Condition1 == Cardinality({ j \in Proc: v[j] = MAX(v)}) > F

RealTermination == Condition1 => Termination

=============================================================================
