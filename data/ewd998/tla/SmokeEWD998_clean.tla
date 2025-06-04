------------------------------- MODULE SmokeEWD998 -------------------------------
EXTENDS EWD998, TLC, Randomization, IOUtils, CSV, FiniteSets

ASSUME TLCGet("config").mode \in {"generate", "simulate"}

k ==
10

SmokeInit ==

\/ /\ active = [n \in Node |-> TRUE]
/\ color = [n \in Node |-> "black"]
/\ counter = [i \in Node |-> 0]
/\ pending = [i \in Node |-> 0]
/\ token = [pos |-> 0, q |-> 0, color |-> ("black")]
\/ /\ pending \in RandomSubset(k, [Node -> 0..(N-1)])
/\ counter \in RandomSubset(k, [Node -> -(N-1)..(N-1)])
/\ active \in RandomSubset(k, [Node -> BOOLEAN])
/\ color \in RandomSubset(k, [Node -> Color])
/\ token \in RandomSubset(k, [pos: Node, q: Node, color: ({"black"})])
/\ Inv!P0

StopAfter ==
TLCGet("config").mode = "simulate" =>

\/ TLCSet("exit", TLCGet("duration") > 1)

\/ TLCSet("exit", TLCGet("diameter") > 100)

BF ==
CHOOSE s \in SUBSET (1..6) : ToString(s) = IOEnv.BF

PN ==
CHOOSE s \in (1..10) : ToString(s) = IOEnv.PN

===============================================================================
