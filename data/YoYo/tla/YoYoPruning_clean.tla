------------------------------ MODULE YoYoPruning ----------------------------

EXTENDS TLC, Integers, FiniteSets, UndirectedGraphs

CONSTANT Nodes, Edges

ASSUME

/\ Nodes \subseteq Int
/\ Nodes # {}
/\ LET G == [node |-> Nodes, edge |-> Edges]
IN  /\ IsUndirectedGraph(G)
/\ IsStronglyConnected(G)

Neighbors(n) == {m \in Nodes : {m,n} \in Edges}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

VARIABLES

active,

phase,

incoming, outgoing,

mailbox

vars == <<active, phase, incoming, outgoing, mailbox>>

kind(n) ==
IF incoming[n] = {} /\ outgoing[n] = {} THEN "leader"
ELSE IF incoming[n] = {} THEN "source"
ELSE IF outgoing[n] = {} THEN "sink"
ELSE "internal"

Messages ==
[phase : {"down"}, sndr : Nodes, val : Nodes] \cup
[phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]
downMsg(s,v) == [phase |-> "down", sndr |-> s, val |-> v]
upMsg(s,r,p) == [phase |-> "up", sndr |-> s, reply |-> r, prune |-> p]

TypeOK ==
/\ active \in [Nodes -> BOOLEAN]
/\ phase \in [Nodes -> {"down", "up"}]
/\ incoming \in [Nodes -> SUBSET Nodes]
/\ \A n \in Nodes : incoming[n] \subseteq Neighbors(n)
/\ outgoing \in [Nodes -> SUBSET Nodes]
/\ \A n \in Nodes : outgoing[n] \subseteq Neighbors(n)
/\ mailbox \in [Nodes -> SUBSET Messages]
/\ \A n \in Nodes : \A msg \in mailbox[n] :
/\ msg.phase = "down" =>
/\ n \in outgoing[msg.sndr]
/\ \A mm \in mailbox[n] :
mm.phase = "down" /\ mm.sndr = msg.sndr => mm = msg
/\ msg.phase = "up" =>
/\ msg.sndr \in outgoing[n]
/\ \A mm \in mailbox[n] :
mm.phase = "up" /\ mm.sndr = msg.sndr => mm = msg

------------------------------------------------------------------------------

Init ==
/\ active = [n \in Nodes |-> TRUE]
/\ phase = [n \in Nodes |-> "down"]
/\ incoming = [n \in Nodes |-> { m \in Neighbors(n) : m < n}]
/\ outgoing = [n \in Nodes |-> { m \in Neighbors(n) : m > n}]
/\ mailbox = [n \in Nodes |-> {}]

------------------------------------------------------------------------------

DownSource(n) ==
/\ active[n]
/\ kind(n) = "source"
/\ phase[n] = "down"
/\ mailbox' = [m \in Nodes |->
IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n,n)}
ELSE mailbox[m]]
/\ phase' = [phase EXCEPT ![n] = "up"]
/\ UNCHANGED <<active, incoming, outgoing>>

DownOther(n) ==
/\ active[n]
/\ kind(n) \in {"internal", "sink"}
/\ phase[n] = "down"
/\ LET downMsgs == {msg \in mailbox[n] : msg.phase = "down"}
IN  /\ {msg.sndr : msg \in downMsgs} = incoming[n]
/\ LET min == Min({msg.val : msg \in downMsgs})
IN mailbox' = [m \in Nodes |->
IF m \in outgoing[n]
THEN mailbox[m] \cup {downMsg(n,min)}
ELSE mailbox[m]]
/\ phase' = [phase EXCEPT ![n] = "up"]
/\ UNCHANGED <<active, incoming, outgoing>>

Down(n) == DownSource(n) \/ DownOther(n)

------------------------------------------------------------------------------

UpSource(n) ==
/\ active[n]
/\ kind(n) = "source"
/\ phase[n] = "up"
/\ LET upMsgs == {msg \in mailbox[n] : msg.phase = "up"}
noSndrs == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
pruned == {msg.sndr : msg \in {mm \in upMsgs : mm.prune}}
IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
/\ mailbox' = [mailbox EXCEPT ![n] = mailbox[n] \ upMsgs]
/\ incoming' = [incoming EXCEPT ![n] = noSndrs \ pruned]
/\ outgoing' = [outgoing EXCEPT ![n] = @ \ (noSndrs \union pruned)]
/\ phase' = [phase EXCEPT ![n] = "down"]
/\ active' = active

UpOther(n) ==
/\ active[n]
/\ kind(n) \in {"internal", "sink"}
/\ phase[n] = "up"
/\ LET upMsgs == {msg \in mailbox[n] : msg.phase = "up"}
noSndrs == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
pruned == {msg.sndr : msg \in {mm \in upMsgs : mm.prune}}
downMsgs == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
valsRcvd == {msg.val : msg \in downMsgs}
senders(v) == {m \in incoming[n] : downMsg(m,v) \in downMsgs}
valSent(m) == (CHOOSE msg \in downMsgs : msg.sndr = m).val
isLoneSink == kind(n) = "sink" /\ Cardinality(incoming[n]) = 1
IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
/\

\E keep \in {f \in [valsRcvd -> incoming[n]] :
\A v \in valsRcvd : f[v] \in senders(v)} :
/\ IF noSndrs = {}
THEN LET min == Min({msg.val : msg \in downMsgs})
minSndrs == {msg.sndr : msg \in {mm \in downMsgs : mm.val = min}}
IN  /\ mailbox' = [m \in Nodes |->
IF m \in incoming[n]
THEN mailbox[m] \union
{upMsg(n,
IF m \in minSndrs THEN "yes" ELSE "no",
(m # keep[valSent(m)]) \/ isLoneSink)}
ELSE IF m = n THEN mailbox[m] \ (upMsgs \union downMsgs)
ELSE mailbox[m]]
/\ incoming' = [incoming EXCEPT ![n] =
IF isLoneSink THEN {} ELSE {keep[min]}]
/\ outgoing' = [outgoing EXCEPT ![n] =
(@ \ pruned) \union
{keep[v] : v \in valsRcvd \ {min}}]
ELSE /\ mailbox' = [m \in Nodes |->
IF m \in incoming[n]
THEN mailbox[m] \union {upMsg(n, "no", m # keep[valSent(m)])}
ELSE IF m = n THEN mailbox[m] \ (upMsgs \union downMsgs)
ELSE mailbox[m]]
/\ incoming' = [incoming EXCEPT ![n] = noSndrs \ pruned]
/\ outgoing' = [outgoing EXCEPT ![n] =
(@ \ (noSndrs \union pruned)) \union
{keep[v] : v \in valsRcvd}]
/\ active' = [active EXCEPT ![n] = ~ isLoneSink]
/\ phase' = [phase EXCEPT ![n] = "down"]

Up(n) == UpSource(n) \/ UpOther(n)

------------------------------------------------------------------------------

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

------------------------------------------------------------------------------

MoreThanOneSource == \E s1, s2 \in Nodes :
s1 # s2 /\ kind(s1) = "source" /\ kind(s2) = "source"

NeighborInv == \A m,n \in Nodes :
m \in outgoing[n] <=>
\/ n \in incoming[m]
\/ /\ n \in outgoing[m]
/\ \/ upMsg(n, "no", FALSE) \in mailbox[m]
\/ upMsg(m, "no", FALSE) \in mailbox[n]
\/ /\ n \notin (incoming[m] \union outgoing[m])
/\ \E r \in {"yes", "no"} : upMsg(m, r, TRUE) \in mailbox[n]

NoNewSource ==
[][\A n \in Nodes : kind(n)' = "source" => kind(n) = "source"]_vars

Termination == \A n \in Nodes :
/\ IF n = Min(Nodes) THEN kind(n) = "leader" ELSE ~ active[n]
/\ mailbox[n] = {}

Liveness == <>Termination
FinishIffTerminated == ~(ENABLED Next) <=> Termination
==============================================================================
