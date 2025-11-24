---- MODULE MultiPaxos ----
******************************)
Model inputs & assumptions. *)
*******************************)
Useful constants & typedefs. *)
*****************************())
Main algorithm in PlusCal. *)
*****************************()
--algorithm MultiPaxos
variable msgs = {},                             \* messages in the network
node = [r \in Replicas |-> NullNode],  \* replica node state
pending = InitPending,                 \* sequence of pending reqs
observed = <<>>;                       \* client observed events
define UnseenPending(insts) == SelectSeq(pending, c -> !c.cmd # insts[Slot].cmd);
RemovePending(cmd) == SelectSeq(pending, c -> c# cmd);
reqsMade = {e.cmd: e in observed | e.type = "Req"};
acksRecv = {e.cmd: e in observed | e.type = "Ack"};
terminated = Len(pending) == 0 /\ Cardinality(reqsMade) == NumCommands /\ Cardinality(acksRecv) == NumCommands;
end define;
Send a set of messages helper.
macro Send(set) begin
msgs := msgs \cup set;
end macro;
Observe a client event helper.
macro Observe(e) begin
observed := observed + e;
end macro;
Leader gathers PrepareReply messages until condition met, then marks the corresponding ballot as prepared and saves highest voted commands.
macro HandlePrepareReplies(r) begin
if I'm waiting for PrepareReplies await node[r].leader = r /\ node[r].balPrepared = 0; when there are enough number of PrepareReply messages with desired ballot do await Cardinality({m \in msgs | m.type == "PrepareReply" && m.ballot >= node[r].maxBallot}) >= MajorityNum marks this ballot as prepared and saves highest voted command in each slot if any node[r].balPrepared := node[r].maxBallot || node[r].insts := [Slot \in Slots | node[r].insts[Slot].status == "Empty"] -> {node[r].insts[Slot] with status = "Accepting" && cmd = PeakVotedCmd({m.slot}, Slot)} end; send Accept messages for in-progress instances Send ({AcceptMsg(r, node[r].balPrepared, s, c): s \in {Slot | node[r].insts[Slot]}.status == "Accepting"}))
end macro;
A prepared leader takes a new request to fill the next empty slot.
macro TakeNewRequest(r) begin
if I'm a prepared leader and there is pending request await node[r].leader = r /\ node[r].balPrepared == node[r].maxBallot \/ \E Slot in Slots: node[r].insts[Slot] .status == "Empty" && Len(UnseenPending({node[r].insts}.slot)) > 0 find the next empty slot and pick a pending request with s = FirstEmptySlot({node[r].insts}) c = Head(UnseenPending({node[r].insts})) W.L.O.G., only pick a command not seen in current prepared log to have smaller state space; In practice, duplicated client requests should be treated by some idempotency mechanism such as using request IDs do update slot status and voted node[{r}.insts][Slot] with status = "Accepting" && cmd = c end; broadcast Accept messages for in-progress instances Send ({AcceptMsg(r, {node[r].balPrepared}, s, c): s \in Slots | node[r].insts[Slot].status == "Accepting"}))
end macro;
Replica receives new commit notification.
macro HandleCommitNotice(r) begin
if I'm a follower waiting on CommitNotice await node[{r}.leader] != r /\ node[{r}.commitUpTo] < NumCommands /\ node[{{r}].insts}[{node[r].commitUpTo+1}] .status == "Accepting" for this slot, when there is a commit notice message with upto do marks this slot as committed and apply command node[r].insts[{m.upto}.slot] with status = "Committed" end;
end macro;
Replica server main loop process Replicas begin rloop: while ~terminated do either BecomeLeader(self); or HandlePrepare(self) or TakeNewRequest(self) or HandleAccept(self) or HandleCommitNotice(self) end either; end while; end process;
end algorithm; *)
====