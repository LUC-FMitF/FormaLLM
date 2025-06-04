----------------------------- MODULE YoYoNoPruning ---------------------------

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

phase,

incoming, outgoing,

mailbox

vars == <<phase, incoming, outgoing, mailbox>>

kind(n) ==
IF incoming[n] = {} THEN "source"
ELSE IF outgoing[n] = {} THEN "sink"
ELSE "internal"

Messages ==
[phase : {"down"}, sndr : Nodes, val : Nodes] \cup
[phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}]
downMsg(s,v) == [phase |-> "down", sndr |-> s, val |-> v]
upMsg(s,r) == [phase |-> "up", sndr |-> s, reply |-> r]

TypeOK ==
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
/\ phase = [n \in Nodes |-> "down"]
/\ incoming = [n \in Nodes |-> { m \in Neighbors(n) : m < n}]
/\ outgoing = [n \in Nodes |-> { m \in Neighbors(n) : m > n}]
/\ mailbox = [n \in Nodes |-> {}]

------------------------------------------------------------------------------

DownSource(n) ==
/\ kind(n) = "source"
/\ phase[n] = "down"
/\ mailbox' = [m \in Nodes |->
IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n,n)}
ELSE mailbox[m]]
/\ phase' = [phase EXCEPT ![n] = "up"]
/\ UNCHANGED <<incoming, outgoing>>

DownOther(n) ==
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
/\ UNCHANGED <<incoming, outgoing>>

Down(n) == DownSource(n) \/ DownOther(n)

------------------------------------------------------------------------------

UpSource(n) ==
/\ kind(n) = "source"
/\ phase[n] = "up"
/\ LET upMsgs == {msg \in mailbox[n] : msg.phase = "up"}
noSndrs == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
/\ mailbox' = [mailbox EXCEPT ![n] = mailbox[n] \ upMsgs]
/\ incoming' = [incoming EXCEPT ![n] = noSndrs]
/\ outgoing' = [outgoing EXCEPT ![n] = @ \ noSndrs]
/\ phase' = [phase EXCEPT ![n] = "down"]

UpOther(n) ==
/\ kind(n) \in {"internal", "sink"}
/\ phase[n] = "up"
/\ LET upMsgs == {msg \in mailbox[n] : msg.phase = "up"}
noSndrs == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
downMsgs == {msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr \in incoming[n]}
IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
/\ IF noSndrs = {}
THEN LET min == Min({msg.val : msg \in downMsgs})
minSndrs == {msg.sndr : msg \in {mm \in downMsgs : mm.val = min}}
IN  /\ mailbox' = [m \in Nodes |->
IF m \in incoming[n]
THEN mailbox[m] \union
{upMsg(n, IF m \in minSndrs THEN "yes" ELSE "no")}
ELSE IF m = n THEN mailbox[m] \ (upMsgs \union downMsgs)
ELSE mailbox[m]]
/\ incoming' = [incoming EXCEPT ![n] = minSndrs]
/\ outgoing' = [outgoing EXCEPT ![n] =
@ \union (incoming[n] \ minSndrs)]
ELSE /\ mailbox' = [m \in Nodes |->
IF m \in incoming[n] THEN mailbox[m] \union {upMsg(n, "no")}
ELSE IF m = n THEN mailbox[m] \ (upMsgs \union downMsgs)
ELSE mailbox[m]]
/\ incoming' = [incoming EXCEPT ![n] = noSndrs]
/\ outgoing' = [outgoing EXCEPT ![n] =
(@ \ noSndrs) \union incoming[n]]
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
/\ upMsg(n, "no") \in mailbox[m] \/ upMsg(m, "no") \in mailbox[n]

NoNewSource ==
[][\A n \in Nodes : kind(n)' = "source" => kind(n) = "source"]_vars

Stabilization ==
/\ kind(Min(Nodes)) = "source"
/\ \A n \in Nodes : kind(n) = "source" => n = Min(Nodes)
/\ \A n \in Nodes : \A msg \in mailbox[n] :
/\ msg.phase = "down" => msg.val = Min(Nodes)
/\ msg.phase = "up" => msg.reply = "yes"

Liveness == <>[]Stabilization
==============================================================================
