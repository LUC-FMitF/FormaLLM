---- MODULE MultiPaxos ----
EXTENDS FiniteSets, Sequences, Integers, TLC

CONSTANT Replicas,
Writes,
Reads,
MaxBallot

ReplicasAssumption == /\ IsFiniteSet(Replicas)
/\ Cardinality(Replicas) >= 1

WritesAssumption == /\ IsFiniteSet(Writes)
/\ Cardinality(Writes) >= 1
/\ "nil" \notin Writes

ReadsAssumption == /\ IsFiniteSet(Reads)
/\ Cardinality(Reads) >= 0
/\ "nil" \notin Writes

MaxBallotAssumption == /\ MaxBallot \in Nat
/\ MaxBallot >= 2

ASSUME /\ ReplicasAssumption
/\ WritesAssumption
/\ ReadsAssumption
/\ MaxBallotAssumption

----------

Commands == Writes \cup Reads

NumCommands == Cardinality(Commands)

Range(seq) == {seq[i]: i \in 1..Len(seq)}

ClientEvents ==      [type: {"Req"}, cmd: Commands]
\cup [type: {"Ack"}, cmd: Commands,
val: {"nil"} \cup Writes]

ReqEvent(c) == [type |-> "Req", cmd |-> c]

AckEvent(c, v) == [type |-> "Ack", cmd |-> c, val |-> v]

InitPending ==    (CHOOSE ws \in [1..Cardinality(Writes) -> Writes]
: Range(ws) = Writes)
\o (CHOOSE rs \in [1..Cardinality(Reads) -> Reads]
: Range(rs) = Reads)

MajorityNum == (Cardinality(Replicas) \div 2) + 1

Ballots == 1..MaxBallot

Slots == 1..NumCommands

Statuses == {"Preparing", "Accepting", "Committed"}

InstStates == [status: {"Empty"} \cup Statuses,
cmd: {"nil"} \cup Commands,
voted: [bal: {0} \cup Ballots,
cmd: {"nil"} \cup Commands]]

NullInst == [status |-> "Empty",
cmd |-> "nil",
voted |-> [bal |-> 0, cmd |-> "nil"]]

NodeStates == [leader: {"none"} \cup Replicas,
kvalue: {"nil"} \cup Writes,
commitUpTo: {0} \cup Slots,
balPrepared: {0} \cup Ballots,
balMaxKnown: {0} \cup Ballots,
insts: [Slots -> InstStates]]

NullNode == [leader |-> "none",
kvalue |-> "nil",
commitUpTo |-> 0,
balPrepared |-> 0,
balMaxKnown |-> 0,
insts |-> [s \in Slots |-> NullInst]]

FirstEmptySlot(insts) ==
CHOOSE s \in Slots:
/\ insts[s].status = "Empty"
/\ \A t \in 1..(s-1): insts[t].status # "Empty"

PrepareMsgs == [type: {"Prepare"}, src: Replicas,
bal: Ballots]

PrepareMsg(r, b) == [type |-> "Prepare", src |-> r,
bal |-> b]

InstsVotes == [Slots -> [bal: {0} \cup Ballots,
cmd: {"nil"} \cup Commands]]

VotesByNode(n) == [s \in Slots |-> n.insts[s].voted]

PrepareReplyMsgs == [type: {"PrepareReply"}, src: Replicas,
bal: Ballots,
votes: InstsVotes]

PrepareReplyMsg(r, b, iv) ==
[type |-> "PrepareReply", src |-> r,
bal |-> b,
votes |-> iv]

PeakVotedCmd(prs, s) ==
IF \A pr \in prs: pr.votes[s].bal = 0
THEN "nil"
ELSE LET bc == CHOOSE bc \in (Ballots \X Commands):
/\ \E pr \in prs: /\ pr.votes[s].bal = bc[1]
/\ pr.votes[s].cmd = bc[2]
/\ \A pr \in prs: pr.votes[s].bal =< bc[1]
IN  bc[2]

AcceptMsgs == [type: {"Accept"}, src: Replicas,
bal: Ballots,
slot: Slots,
cmd: Commands]

AcceptMsg(r, b, s, c) == [type |-> "Accept", src |-> r,
bal |-> b,
slot |-> s,
cmd |-> c]

AcceptReplyMsgs == [type: {"AcceptReply"}, src: Replicas,
bal: Ballots,
slot: Slots]

AcceptReplyMsg(r, b, s) == [type |-> "AcceptReply", src |-> r,
bal |-> b,
slot |-> s]

CommitNoticeMsgs == [type: {"CommitNotice"}, upto: Slots]

CommitNoticeMsg(u) == [type |-> "CommitNotice", upto |-> u]

Messages ==      PrepareMsgs
\cup PrepareReplyMsgs
\cup AcceptMsgs
\cup AcceptReplyMsgs
\cup CommitNoticeMsgs

----------

----------

VARIABLES msgs, node, pending, observed, pc

UnseenPending(insts) ==
LET filter(c) == c \notin {insts[s].cmd: s \in Slots}
IN  SelectSeq(pending, filter)

RemovePending(cmd) ==
LET filter(c) == c # cmd
IN  SelectSeq(pending, filter)

reqsMade == {e.cmd: e \in {e \in Range(observed): e.type = "Req"}}

acksRecv == {e.cmd: e \in {e \in Range(observed): e.type = "Ack"}}

terminated == /\ Len(pending) = 0
/\ Cardinality(reqsMade) = NumCommands
/\ Cardinality(acksRecv) = NumCommands

vars == << msgs, node, pending, observed, pc >>

ProcSet == (Replicas)

Init ==
/\ msgs = {}
/\ node = [r \in Replicas |-> NullNode]
/\ pending = InitPending
/\ observed = <<>>
/\ pc = [self \in ProcSet |-> "rloop"]

rloop(self) == /\ pc[self] = "rloop"
/\ IF ~terminated
THEN /\ \/ /\ node[self].leader # self
/\ \E b \in Ballots:
/\ /\ b > node[self].balMaxKnown
/\ ~\E m \in msgs: (m.type = "Prepare") /\ (m.bal = b)
/\ node' = [node EXCEPT ![self].leader = self,
![self].balPrepared = 0,
![self].balMaxKnown = b,
![self].insts = [s \in Slots |->
[node[self].insts[s]
EXCEPT !.status = IF @ = "Accepting"
THEN "Preparing"
ELSE @]]]
/\ msgs' = (msgs \cup ({PrepareMsg(self, b),
PrepareReplyMsg(self, b, VotesByNode(node'[self]))}))
/\ UNCHANGED <<pending, observed>>
\/ /\ \E m \in msgs:
/\ /\ m.type = "Prepare"
/\ m.bal > node[self].balMaxKnown
/\ node' = [node EXCEPT ![self].leader = m.src,
![self].balMaxKnown = m.bal,
![self].insts = [s \in Slots |->
[node[self].insts[s]
EXCEPT !.status = IF @ = "Accepting"
THEN "Preparing"
ELSE @]]]
/\ msgs' = (msgs \cup ({PrepareReplyMsg(self, m.bal, VotesByNode(node'[self]))}))
/\ UNCHANGED <<pending, observed>>
\/ /\ /\ node[self].leader = self
/\ node[self].balPrepared = 0
/\ LET prs == {m \in msgs: /\ m.type = "PrepareReply"
/\ m.bal = node[self].balMaxKnown} IN
/\ Cardinality(prs) >= MajorityNum
/\ node' = [node EXCEPT ![self].balPrepared = node[self].balMaxKnown,
![self].insts = [s \in Slots |->
[node[self].insts[s]
EXCEPT !.status = IF \/ @ = "Preparing"
\/ /\ @ = "Empty"
/\ PeakVotedCmd(prs, s) # "nil"
THEN "Accepting"
ELSE @,
!.cmd = PeakVotedCmd(prs, s)]]]
/\ msgs' = (msgs \cup ({AcceptMsg(self, node'[self].balPrepared, s, node'[self].insts[s].cmd):
s \in {s \in Slots: node'[self].insts[s].status = "Accepting"}}))
/\ UNCHANGED <<pending, observed>>
\/ /\ /\ node[self].leader = self
/\ node[self].balPrepared = node[self].balMaxKnown
/\ \E s \in Slots: node[self].insts[s].status = "Empty"
/\ Len(UnseenPending(node[self].insts)) > 0
/\ LET s == FirstEmptySlot(node[self].insts) IN
LET c == Head(UnseenPending(node[self].insts)) IN
/\ node' = [node EXCEPT ![self].insts[s].status = "Accepting",
![self].insts[s].cmd = c,
![self].insts[s].voted.bal = node[self].balPrepared,
![self].insts[s].voted.cmd = c]
/\ msgs' = (msgs \cup ({AcceptMsg(self, node'[self].balPrepared, s, c),
AcceptReplyMsg(self, node'[self].balPrepared, s)}))
/\ IF (ReqEvent(c)) \notin Range(observed)
THEN /\ observed' = Append(observed, (ReqEvent(c)))
ELSE /\ TRUE
/\ UNCHANGED observed
/\ UNCHANGED pending
\/ /\ \E m \in msgs:
/\ /\ m.type = "Accept"
/\ m.bal >= node[self].balMaxKnown
/\ m.bal > node[self].insts[m.slot].voted.bal
/\ node' = [node EXCEPT ![self].leader = m.src,
![self].balMaxKnown = m.bal,
![self].insts[m.slot].status = "Accepting",
![self].insts[m.slot].cmd = m.cmd,
![self].insts[m.slot].voted.bal = m.bal,
![self].insts[m.slot].voted.cmd = m.cmd]
/\ msgs' = (msgs \cup ({AcceptReplyMsg(self, m.bal, m.slot)}))
/\ UNCHANGED <<pending, observed>>
\/ /\ /\ node[self].leader = self
/\ node[self].balPrepared = node[self].balMaxKnown
/\ node[self].commitUpTo < NumCommands
/\ node[self].insts[node[self].commitUpTo+1].status = "Accepting"
/\ LET s == node[self].commitUpTo + 1 IN
LET c == node[self].insts[s].cmd IN
LET v == node[self].kvalue IN
LET ars == {m \in msgs: /\ m.type = "AcceptReply"
/\ m.slot = s
/\ m.bal = node[self].balPrepared} IN
/\ Cardinality(ars) >= MajorityNum
/\ node' = [node EXCEPT ![self].insts[s].status = "Committed",
![self].commitUpTo = s,
![self].kvalue = IF c \in Writes THEN c ELSE @]
/\ IF (AckEvent(c, v)) \notin Range(observed)
THEN /\ observed' = Append(observed, (AckEvent(c, v)))
ELSE /\ TRUE
/\ UNCHANGED observed
/\ pending' = RemovePending(c)
/\ msgs' = (msgs \cup ({CommitNoticeMsg(s)}))
\/ /\ /\ node[self].leader # self
/\ node[self].commitUpTo < NumCommands
/\ node[self].insts[node[self].commitUpTo+1].status = "Accepting"
/\ LET s == node[self].commitUpTo + 1 IN
LET c == node[self].insts[s].cmd IN
\E m \in msgs:
/\ /\ m.type = "CommitNotice"
/\ m.upto = s
/\ node' = [node EXCEPT ![self].insts[s].status = "Committed",
![self].commitUpTo = s,
![self].kvalue = IF c \in Writes THEN c ELSE @]
/\ UNCHANGED <<msgs, pending, observed>>
/\ pc' = [pc EXCEPT ![self] = "rloop"]
ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
/\ UNCHANGED << msgs, node, pending, observed >>

Replica(self) == rloop(self)

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
/\ UNCHANGED vars

Next == (\E self \in Replicas: Replica(self))
\/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

====
