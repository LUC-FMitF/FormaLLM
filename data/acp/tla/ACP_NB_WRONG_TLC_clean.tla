--------------------------- MODULE ACP_NB_WRONG_TLC ----------------------------

EXTENDS ACP_SB

--------------------------------------------------------------------------------

TypeInvParticipantNB  == participant \in  [
participants -> [
vote      : {yes, no},
alive     : BOOLEAN,
decision  : {undecided, commit, abort},
faulty    : BOOLEAN,
voteSent  : BOOLEAN,
forward   : [ participants -> {notsent, commit, abort} ]
]
]

TypeInvNB == TypeInvParticipantNB /\ TypeInvCoordinator

--------------------------------------------------------------------------------

InitParticipantNB == participant \in [
participants -> [
vote     : {yes, no},
alive    : {TRUE},
decision : {undecided},
faulty   : {FALSE},
voteSent : {FALSE},
forward  : [ participants -> {notsent} ]
]
]

InitNB == InitParticipantNB /\ InitCoordinator

--------------------------------------------------------------------------------

forward(i,j) == /\ i # j
/\ participant[i].alive
/\ participant[i].decision # notsent
/\ participant[i].forward[j] = notsent
/\ participant' = [participant EXCEPT ![i] =
[@ EXCEPT !.forward =
[@ EXCEPT ![j] = participant[i].decision]
]
]
/\ UNCHANGED<<coordinator>>

decideOnForward(i,j) == /\ i # j
/\ participant[i].alive
/\ participant[i].decision = undecided
/\ participant[j].forward[i] # notsent
/\ participant' = [participant EXCEPT ![i] =
[@ EXCEPT !.decision = participant[j].forward[i]]
]
/\ UNCHANGED<<coordinator>>

abortOnTimeout(i) == /\ participant[i].alive
/\ participant[i].decision = undecided
/\ ~coordinator.alive
/\ \A j \in participants : participant[j].alive => coordinator.broadcast[j] = notsent
/\ \A j,k \in participants : ~participant[j].alive /\ participant[k].alive => participant[j].forward[k] = notsent
/\ participant' = [participant EXCEPT ![i] = [@ EXCEPT !.decision = abort]]
/\ UNCHANGED<<coordinator>>

---------------------------------------------------------------------------------

parProgNB(i,j) == \/ parProg(i)
\/ forward(i,j)
\/ decideOnForward(i,j)
\/ abortOnTimeout(i)

parProgNNB == \E i,j \in participants : parDie(i) \/ parProgNB(i,j)

progNNB == parProgNNB \/ coordProgN

fairnessNB == /\ \A i \in participants : WF_<<coordinator, participant>>(\E j \in participants : parProgNB(i,j))
/\ WF_<<coordinator, participant>>(coordProgB)

SpecNB == InitNB /\ [][progNNB]_<<coordinator, participant>> /\ fairnessNB

================================================================================
