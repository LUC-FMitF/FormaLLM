------------------------------ MODULE bcastFolklore ------------------------------

EXTENDS Naturals

CONSTANTS N, T, F

VARIABLES Corr,
nCrashed,
pc,
rcvd,
sent

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat
ASSUME (N > 2 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }

vars == << pc, rcvd, sent, nCrashed, Corr >>

Init ==
/\ nCrashed = 0
/\ Corr = 1 .. N
/\ sent = {}
/\ pc \in [ Proc -> {"V0", "V1"} ]
/\ rcvd = [ i \in Proc |-> {} ]

InitNoBcast ==
/\ nCrashed = 0
/\ Corr = 1 .. N
/\ sent = {}
/\ pc = [ p \in Proc |-> "V0" ]
/\ rcvd = [ i \in Proc |-> {} ]

Receive(self) ==
/\ pc[self] # "CR"
/\ \E msgs \in SUBSET (Proc \times M):
/\ msgs \subseteq sent
/\ rcvd[self] \subseteq msgs
/\ rcvd' = [rcvd EXCEPT ![self] = msgs ]

UponV1(self) ==
/\ pc[self] = "V1"
/\ pc' = [pc EXCEPT ![self] = "AC"]
/\ sent' = sent \cup { <<self, "ECHO">> }
/\ nCrashed' = nCrashed
/\ Corr' = Corr

UponAccept(self) ==
/\ (pc[self] = "V0" \/ pc[self] = "V1")
/\ rcvd'[self] # {}
/\ pc' = [pc EXCEPT ![self] = "AC"]
/\ sent' = sent \cup { <<self, "ECHO">> }
/\ nCrashed' = nCrashed
/\ Corr' = Corr

UponCrash(self) ==
/\ nCrashed < F
/\ pc[self] # "CR"
/\ nCrashed' = nCrashed + 1
/\ pc' = [pc EXCEPT ![self] = "CR"]
/\ sent' = sent
/\ Corr' = Corr \ { self }

Step(self) ==
/\ Receive(self)
/\ \/ UponV1(self)
\/ UponAccept(self)
\/ UponCrash(self)
\/ UNCHANGED << pc, sent, nCrashed, Corr >>

Next ==  (\E self \in Corr: Step(self))

Spec == Init /\ [][Next]_vars
/\ WF_vars(\E self \in Corr: /\ Receive(self)
/\ \/ UponV1(self)
\/ UponAccept(self)
\/ UNCHANGED << pc, sent, nCrashed, Corr >> )

SpecNoBcast == InitNoBcast /\ [][Next]_vars
/\ WF_vars(\E self \in Corr: /\ Receive(self)
/\ \/ UponV1(self)
\/ UponAccept(self)
\/ UNCHANGED << pc, sent, nCrashed, Corr >> )

TypeOK ==
/\ sent \in SUBSET (Proc \times M)
/\ pc \in [ Proc -> {"V0", "V1", "AC", "CR"} ]
/\ rcvd \in [ Proc -> SUBSET (Proc \times M) ]
/\ nCrashed \in 0..N
/\ Corr \in SUBSET Proc

UnforgLtl == (\A i \in Corr: pc[i] = "V0") => [](\A i \in Corr: pc[i] /= "AC")

Unforg == (\A self \in Corr: (pc[self] /= "AC"))

CorrLtl == (\A i \in Corr: pc[i] = "V1") => <>(\E i \in Corr: pc[i] = "AC")

RelayLtl == []((\E i \in Corr: pc[i] = "AC") => <>(\A i \in Corr: pc[i] = "AC"))

ReliableChan ==
[]( \E sndr \in 1..N : (<<sndr, "ECHO">> \in sent
=> <>[](\A p \in Corr : <<sndr, "ECHO">> \in rcvd[p])))

=============================================================================
