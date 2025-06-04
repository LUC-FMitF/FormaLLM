------------------------------ MODULE nbacc_ray97 ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES pc,
rcvd,
sent,
fd

ASSUME N \in Nat

Proc == 1 .. N

M == { "YES", "NO" }

vars == << pc, rcvd, sent, fd >>

Receive(self) ==
\E r \in SUBSET (Proc \times M):
/\ r \subseteq sent
/\ rcvd[self] \subseteq r
/\ rcvd' = [rcvd EXCEPT ![self] = r ]

UpdateFailureDetector(self) ==
\/  fd' = [fd EXCEPT ![self] = FALSE ]
\/  fd' = [fd EXCEPT ![self] = TRUE ]

UponCrash(self) ==
/\ pc[self] # "CRASH"
/\ pc' = [pc EXCEPT ![self] = "CRASH"]
/\ sent' = sent

UponYes(self) ==
/\ pc[self] = "YES"
/\ pc' = [pc EXCEPT ![self] = "SENT"]
/\ sent' = sent \cup { <<self, "YES">> }

UponNo(self) ==
/\ pc[self] = "NO"
/\ pc' = [pc EXCEPT ![self] = "SENT"]
/\ sent' = sent \cup { <<self, "NO">> }

UponSent(self) ==
/\ pc[self] = "SENT"
/\ ( \/ ( /\ fd'[self] = TRUE
/\ pc' = [pc EXCEPT ![self] = "ABORT"] )
\/ ( /\ \E msg \in rcvd[self] : msg[2] = "NO"
/\ pc' = [pc EXCEPT ![self] = "ABORT"] )
\/ ( /\ fd'[self] = FALSE
/\ { p \in Proc : ( \E msg \in rcvd'[self] : msg[1] = p /\ msg[2] = "YES") } = Proc
/\ pc' = [pc EXCEPT ![self] = "COMMIT"] ) )
/\ sent' = sent

Step(self) ==
/\ Receive(self)
/\ UpdateFailureDetector(self)
/\ \/ UponYes(self)
\/ UponNo(self)
\/ UponCrash(self)
\/ UponSent(self)
\/ pc' = pc /\ sent' = sent

Init ==
/\ sent = {}
/\ pc \in [ Proc -> {"YES", "NO"} ]
/\ rcvd = [ i \in Proc |-> {} ]
/\ fd \in [ Proc -> {FALSE, TRUE} ]

InitAllYes ==
/\ sent = {}
/\ pc = [ Proc |-> "YES" ]
/\ rcvd = [ i \in Proc |-> {} ]
/\ fd \in [ i \in Proc |-> {TRUE} ]

Next ==  (\E self \in Proc : Step(self))

Spec == Init /\ [][Next]_vars
/\ WF_vars(\E self \in Proc : /\ Receive(self)
/\ \/ UponYes(self)
\/ UponNo(self)
\/ UponSent(self))

TypeOK ==
/\ sent \subseteq Proc \times M
/\ pc \in [ Proc -> {"NO", "YES", "ABORT", "COMMIT", "SENT", "CRASH"} ]
/\ rcvd \in [ Proc -> SUBSET (Proc \times M) ]
/\ fd \in [ Proc -> BOOLEAN ]

Validity ==
\/ \A i \in Proc : pc[i] = "YES"
\/ \A i \in Proc : pc[i] # "COMMIT"

=============================================================================
