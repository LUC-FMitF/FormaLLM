------------------------------ MODULE nbacg_guer01 ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES nSntNo,
nSntYes,
nSntNoF,
nSntYesF,
nRcvdYes,
nRcvdNo,
someFail,
pc

Proc == 1 .. N
Status == { "YES", "NO", "SENT", "ABORT", "COMMIT", "BYZ" }
vars == << nSntNo, nSntYes, nSntYesF, nSntNoF, nRcvdNo, nRcvdYes, someFail, pc >>

Init ==
/\ nSntNo = 0
/\ nSntYes = 0
/\ nSntNoF = 0
/\ nSntYesF = 0
/\ nRcvdYes = [ i \in Proc |-> 0 ]
/\ nRcvdNo = [ i \in Proc |-> 0 ]
/\ pc \in [ Proc -> { "NO", "YES" } ]
/\ someFail \in [ Proc -> BOOLEAN ]

InitYes ==
/\ nSntNo = 0
/\ nSntYes = 0
/\ nSntNoF = 0
/\ nSntYesF = 0
/\ nRcvdYes = [ i \in Proc |-> 0 ]
/\ nRcvdNo = [ i \in Proc |-> 0 ]
/\ pc \in [ Proc -> { "YES" } ]
/\ someFail \in [ Proc -> BOOLEAN ]

InitNo ==
/\ nSntNo = 0
/\ nSntYes = 0
/\ nSntNoF = 0
/\ nSntYesF = 0
/\ nRcvdYes = [ i \in Proc |-> 0 ]
/\ nRcvdNo = [ i \in Proc |-> 0 ]
/\ pc \in [ Proc -> { "NO" } ]
/\ someFail \in [ Proc -> BOOLEAN ]

Crash(i) ==
/\ pc[i] # "BYZ"
/\ pc' = [ pc EXCEPT ![i] = "BYZ" ]
/\ IF pc[i] = "YES"
THEN nSntYesF' = nSntYesF + 1
ELSE nSntYesF' = nSntYesF
/\ IF pc[i] = "NO"
THEN nSntNoF' = nSntNoF + 1
ELSE nSntNoF' = nSntNoF
/\ UNCHANGED << nSntNo, nSntYes, nRcvdNo, nRcvdYes, someFail >>

Receive(i) ==
\/ /\ pc[i] = "SENT"
/\ nRcvdYes[i] < nSntYes + nSntYesF
/\ nRcvdYes' = [ nRcvdYes EXCEPT ![i] = nRcvdYes[i] + 1 ]
/\ UNCHANGED << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdNo, someFail, pc >>
\/ /\ pc[i] = "SENT"
/\ nRcvdNo[i] < nSntNo + nSntNoF
/\ nRcvdNo' = [ nRcvdNo EXCEPT ![i] = nRcvdNo[i] + 1 ]
/\ UNCHANGED << nSntYes, nSntNo, nSntYesF, nSntNoF, nRcvdYes, someFail, pc >>
\/ /\ pc[i] = "SENT"
/\ nRcvdYes[i] =  nSntYes + nSntYesF
/\ nRcvdNo[i] = nSntNo + nSntNoF
/\ UNCHANGED vars

SendYes(i) ==
/\ pc[i] = "YES"
/\ someFail[i] = FALSE
/\ pc' = [ pc EXCEPT ![i] = "SENT" ]
/\ nSntYes' = nSntYes + 1
/\ UNCHANGED << nSntNo, nSntYesF, nSntNoF, nRcvdNo, nRcvdYes, someFail >>

SendNo(i) ==
/\ pc[i] = "NO"
/\ someFail[i] = FALSE
/\ pc' = [ pc EXCEPT ![i] = "SENT" ]
/\ nSntNo' = nSntNo + 1
/\ UNCHANGED << nSntYes, nSntYesF, nSntNoF, nRcvdNo, nRcvdYes, someFail >>

AbortNoYes(i) ==
/\ someFail[i] = TRUE
/\ \/ pc[i] = "YES"
\/ pc[i] = "NO"
/\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
/\ UNCHANGED << nSntNo, nSntYes, nSntYesF, nSntNoF, nRcvdNo, nRcvdYes, someFail >>

AbortSent(i) ==
/\ pc[i] = "SENT"
/\ nRcvdNo[i] > 0
/\ pc' = [ pc EXCEPT ![i] = "ABORT" ]
/\ UNCHANGED << nSntNo, nSntYes, nSntYesF, nSntNoF, nRcvdNo, nRcvdYes, someFail >>

Commit(i) ==
/\ pc[i] = "SENT"
/\ nRcvdNo[i] = 0
/\ nRcvdYes[i] >= N
/\ pc' = [ pc EXCEPT ![i] = "COMMIT" ]
/\ UNCHANGED << nSntNo, nSntYes, nSntYesF, nSntNoF, nRcvdNo, nRcvdYes, someFail >>

Next ==
/\ \E self \in Proc :
\/ Crash(self)
\/ Receive(self)
\/ SendYes(self)
\/ SendNo(self)
\/ AbortNoYes(self)
\/ AbortSent(self)
\/ Commit(self)
\/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
/\ WF_vars(\E self \in Proc :
\/ Receive(self)
\/ SendYes(self)
\/ SendNo(self)
\/ AbortNoYes(self)
\/ AbortSent(self)
\/ Commit(self))

SpecYes == InitYes /\ [][Next]_vars
/\ WF_vars(\E self \in Proc :
\/ Receive(self)
\/ SendYes(self)
\/ SendNo(self)
\/ AbortNoYes(self)
\/ AbortSent(self)
\/ Commit(self))

SpecNo == InitNo /\ [][Next]_vars
/\ WF_vars(\E self \in Proc :
\/ Receive(self)
\/ SendYes(self)
\/ SendNo(self)
\/ AbortNoYes(self)
\/ AbortSent(self)
\/ Commit(self))

TypeOK ==
/\ nSntNo \in 0..N
/\ nSntYes \in 0..N
/\ nSntNoF \in 0..N
/\ nSntYesF \in 0..N
/\ nRcvdYes \in [ Proc -> 0..(nSntYes + nSntYesF) ]
/\ nRcvdNo \in [ Proc -> 0..(nSntNo + nSntNoF) ]
/\ pc \in [ Proc -> Status ]
/\ someFail \in [ Proc -> BOOLEAN ]

AgrrLtl ==
[](~(\E i \in Proc, j \in Proc :  pc[i] = "COMMIT" /\ pc[j] = "ABORT"))

AbortValidityLtl ==
(\E i \in Proc : pc[i] = "NO") => [](\A i \in Proc : pc[i] # "COMMIT")

CommitValidityLtl ==
(\A i \in Proc : pc[i] = "YES" /\ someFail[i] = FALSE) => [](\A i \in Proc : pc[i] = "BYZ" \/ pc[i] # "ABORT")

TerminationLtl ==
([](\A i \in Proc : pc[i] # "BYZ" /\ someFail[i] = FALSE)) => <>(\A i \in Proc : pc[i] = "COMMIT" \/ pc[i] = "ABORT")

=============================================================================
