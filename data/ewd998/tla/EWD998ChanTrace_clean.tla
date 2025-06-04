--------------------------- MODULE EWD998ChanTrace --------------------------
EXTENDS EWD998Chan, Json, TLC, IOUtils, VectorClocks

ASSUME TLCGet("config").mode = "bfs"

JsonLog ==

ndJsonDeserialize(IF "JSON" \in DOMAIN IOEnv THEN IOEnv.JSON ELSE "specifications/ewd998/EWD998ChanTrace.ndjson")

TraceN ==

JsonLog[1].N

TraceLog ==

LET suffix == SubSeq(JsonLog, 2, Len(JsonLog))

IN CausalOrder(suffix,
LAMBDA l : l.pkt.vc,

LAMBDA l : ToString(l.node), LAMBDA vc : DOMAIN vc)

-----------------------------------------------------------------------------

TraceInit ==
/\ Init!1
/\ Init!2

/\ active \in [Node -> {TRUE}]
/\ color \in [Node -> {"white"}]

TraceSpec ==

TraceInit /\ [][Next \/ UNCHANGED vars]_vars

-----------------------------------------------------------------------------

PayloadPred(msg) ==
msg.type = "pl"

IsInitiateToken(l) ==

/\ l.event = ">"

/\ l.pkt.msg.type = "tok"

/\ l.pkt.rcv = N - 1
/\ l.pkt.snd = 0
/\ <<InitiateProbe>>_vars

IsPassToken(l) ==

/\ l.event = ">"

/\ l.pkt.msg.type = "tok"
/\ LET snd == l.pkt.snd IN

/\ l.pkt.snd > 0
/\ <<PassToken(snd)>>_vars

IsRecvToken(l) ==

/\ l.event = "<"
/\ LET msg == l.pkt.msg
rcv == l.pkt.rcv IN

/\ msg.type = "tok"

/\ \A n \in Node:
SelectSeq(inbox[n], PayloadPred) = SelectSeq(inbox'[n], PayloadPred)

/\ \E idx \in DOMAIN inbox'[rcv]:
/\ inbox'[rcv][idx].type = "tok"
/\ inbox'[rcv][idx].q = msg.q
/\ inbox'[rcv][idx].color = msg.color
/\ UNCHANGED <<active, counter, color>>

IsSendMsg(l) ==

/\ l.event = ">"

/\ l.pkt.msg.type = "pl"
/\ <<SendMsg(l.pkt.snd)>>_vars
/\ LET rcv == l.pkt.rcv IN

Len(SelectSeq(inbox[rcv], PayloadPred)) < Len(SelectSeq(inbox'[rcv], PayloadPred))

IsRecvMsg(l) ==

/\ l.event = "<"
/\ l.pkt.msg .type = "pl"
/\ <<RecvMsg(l.pkt.rcv)>>_vars

IsDeactivate(l) ==

/\ l.event = "d"
/\ <<Deactivate(l.node)>>_vars

IsTrm(l) ==

/\ l.event \in {"<", ">"}
/\ l.pkt.msg.type = "trm"

/\ \A n \in Node: ~active[n]

/\ UNCHANGED vars

TraceNextConstraint ==

LET i == TLCGet("level")
IN
/\ i <= Len(TraceLog)
/\ LET logline == TraceLog[i]
IN

BP::
/\ \/ IsInitiateToken(logline)
\/ IsPassToken(logline)
\/ IsRecvToken(logline)
\/ IsSendMsg(logline)
\/ IsRecvMsg(logline)
\/ IsDeactivate(logline)
\/ IsTrm(logline)

/\ "failure" \notin DOMAIN logline

TraceInv ==
LET l == TraceLog[TLCGet("level")] IN
/\ "failure" \notin DOMAIN l
/\ (l.event \in {"<", ">"} /\ l.pkt.msg.type = "trm") => \A n \in Node: ~active[n]

-----------------------------------------------------------------------------

TraceView ==

<<vars, TLCGet("level")>>

-----------------------------------------------------------------------------

TraceAccepted ==

LET d == TLCGet("stats").diameter IN
IF d - 1 = Len(TraceLog) THEN TRUE
ELSE Print(<<"Failed matching the trace to (a prefix of) a behavior:", TraceLog[d],
"TLA+ debugger breakpoint hit count " \o ToString(d+1)>>, FALSE)

-----------------------------------------------------------------------------

TraceAlias ==

[

log     |-> <<TLCGet("level"), TraceLog[TLCGet("level") - 1]>>,
active  |-> active,
color   |-> color,
counter |-> counter,
inbox   |-> inbox,
term    |-> <<EWD998!terminationDetected, "=>", EWD998!Termination>>,
enabled |->
[
InitToken  |-> ENABLED InitiateProbe,
PassToken  |-> ENABLED \E i \in Node \ {0} : PassToken(i),
SendMsg    |-> ENABLED \E i \in Node : SendMsg(i),
RecvMsg    |-> ENABLED \E i \in Node : RecvMsg(i),
Deactivate |-> ENABLED \E i \in Node : Deactivate(i)
]
]

=============================================================================

Tips & Tricks for writing TLA+ "trace specs"
--------------------------------------------

1.  If the postcondition  TraceAccepted  is violated, adding a TLA+ debugger
breakpoint on the line  TraceAccepted!BP  with a hit count value copied from
TLC's error message, is the first step towards diagnosing the divergence.
a) In the TLA+ debugger, enter the  TraceAlias  as a "WATCH" expression.
Especially the  enabled  field helped me figure out why a trace was not
accepted.
b) Enter the  TraceLog  as another "WATCH" expression to show the trace log
in the TLA+ debugger.  Remember, the trace log file may not be in vector
clock order.

2.  A trace ideally maps to a single TLA+ behavior, but we may use non-determinism
in the TLA+ trace spec to fill the holes of a partial/incomplete log, which can
cause the trace to be mapped to multiple TLA+ behaviors.  A *buggy* trace spec
is another reason why a trace is mapped to more than one behavior.  To find the
states with multiple successor states, we found the following two techniques
useful:
a) The TLA+ debugger can be used to find states with multiple successor
states.  Set *inline* breakpoints with a hit count of 2 on all actions
of the high-level spec, or the actions suspected of having multiple
successors.  The TLA+ debugger will stop at the first state with multiple
successors.  An inline breakpoint is a breakpoint set on the right-hand
side of an action definition, i.e., the  SendMsg  in the definition
SendMsg(i) == /\ ...
b) For short traces, having TLC dump the state graph to a GraphViz file
can be useful.  The GraphViz file can be generated by setting the
-dump dot  option of TLC to a file name, e.g.,  -dump dot out.dot
When combined with an ordinary breakpoint of the TLA+ debugger at the
top of  TraceNextConstraint  , dumping the state graph with
-dump dot,snapshot  will cause TLC to create a snapshot of the current
state graph every time the TLA+ debugger stops at the breakpoint.

Shell snippets
--------------

$ alias tlc
tlc='java -cp /path/to/tla2tools.jar tlc2.TLC'

$ javac -cp impl/lib/gson-2.8.6.jar -d impl/bin impl/src/*.java
$ while true; do
T=trace-$(date +%s).ndjson
## Generate a system trace and save if to trace.ndjson.
java -cp impl/bin:impl/lib/gson-2.8.6.jar EWD998App 1 | tee $T
## Validate the system trace (break if the trace fails validation).
JSON=$T tlc -noTE EWD998ChanTrace || break
## Remove T if the trace was accepted.
rm $T
## Wait a few seconds for the OS to reclaim resources.
sleep 3;
done

TODOs
-----

A)
Check how useful spec coverage of EWD998Chan is to determine if we've
seen enough traces => This would suggest to make it possible to check
a set of traces instead of single traces one by one, or make it possible
to merge multiple coverage statistics originating from multiple TLC runs
(IIRC Jesse requested this one => find Github issue^1).  Fundamentally, a set
of traces isn't hard; just add another variable or TLCGet("...") cleverness
to the spec that equals the particular trace "id".  However, the json log is
current not set up for this because we wouldn't know where one trace in
the log file starts and ends, unless we parse the whole log.  For this,
non newline-delim json is probably the better choice.

^1 TLC should expose coverage statistics via, e.g., TLCGet("stats"). Users
can then "dump" its output in a TLC post condition.  Afterward, multiple
dumps can be combined either in TLA+ with e.g. a bit of repl'ing or in
json.

B)
TLC prints the last log line when the trace cannot be mapped to any
behavior in the spec's set of behaviors.  This is good enough for now,
especially when combined with the TLA+ debugger.  However, users might
prefer to see the prefix of the behavior that was mapped, up to the point
where it failed.  For long traces, this might be prohibitively expensive,
though, in which case we could show a suffix of the prefix.

C)
TLC could provide a new mode that would allow to check a set of traces.  Such
a mode could eliminate the need for the  TraceAccepted  ,  TraceView  formulas,
and allow the removal of a few subformulas elsewhere.  However, a new mode
won't signicantly simplify a trace spec, but TLC could report a proper error
trace for the longest trace prefix it accepted.  A simpler "hack" would be
to somehow expose the last state, and, thus, trace in the post condition. Also,
the mode could warn users if  TraceNextConstraint  does not constrain all variables.
