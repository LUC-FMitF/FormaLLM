------------------------------- MODULE EWD998Chan_opts -------------------------------
EXTENDS EWD998Chan, TLC, TLCExt, IOUtils, CSV

ASSUME TLCGet("config").mode = "generate"

ASSUME TLCGet("config").depth = -1

ASSUME TLCGet("config").deadlock = FALSE

ASSUME TLCGet("revision").timestamp >= 1628119427

--------------------------------------------------------------------------------

FeatureFlags ==
{"pt1","pt2","pt3","pt4"}

CONSTANT F
ASSUME F \subseteq FeatureFlags

--------------------------------------------------------------------------------

InitSim ==

/\ active = [n \in Node |-> TRUE]
/\ color = [n \in Node |-> "white"]

PassTokenOpts(n) ==
/\ n # 0

/\ \/ ~ active[n]
\/ /\ "pt1" \in F
/\ color[n] = "black"
\/ /\ "pt2" \in F
/\ \E j \in 1..Len(inbox[n]) : inbox[n][j].type = "tok" /\ inbox[n][j].color = "black"
/\ \E j \in 1..Len(inbox[n]) :
/\ inbox[n][j].type = "tok"

/\ LET tkn == inbox[n][j]
IN  inbox' = [inbox EXCEPT ![CASE "pt3" \in F /\ color[n] = "black" -> 0
[] "pt4" \in F /\ tkn.color ="black" -> 0
[] OTHER    ->  n-1] =
Append(@, [tkn EXCEPT !.q = tkn.q + counter[n],
!.color = IF color[n] = "black"
THEN "black"
ELSE tkn.color]),
![n] = RemoveAt(@, j) ]

/\ color' = [ color EXCEPT ![n] = "white" ]

/\ UNCHANGED <<active, counter>>

SystemOpts(n) == \/ InitiateProbe
\/ PassTokenOpts(n)

SpecOpts == InitSim /\ Init /\ [][\E n \in Node: SystemOpts(n) \/ Environment]_vars

--------------------------------------------------------------------------------

ASSUME TLCSet(1, 0)

AtTermination ==
IF EWD998!Termination # EWD998!Termination'
THEN TLCSet(1, TLCGet("level"))
ELSE TRUE

AtTerminationDetected ==

EWD998!terminationDetected =>
/\ LET o == TLCGet("stats").behavior.actions
IN
/\ CSVWrite("%1$s#%2$s#%3$s#%4$s#%5$s#%6$s#%7$s#%8$s#%9$s#%10$s",
<< F, N, TLCGet("level"), TLCGet(1), TLCGet("level") - TLCGet(1),
o["InitiateProbe"],o["PassTokenOpts"],
o["SendMsg"],o["RecvMsg"],o["Deactivate"]
>>,
IOEnv.Out)

/\ TLCSet(1, 0)

--------------------------------------------------------------------------------

Features ==
CHOOSE s \in SUBSET FeatureFlags : ToString(s) = IOEnv.F

Nodes ==
CHOOSE n \in 1..256 : ToString(n) = IOEnv.N

================================================================================

------------------------------ CONFIG EWD998_opts ------------------------------
CONSTANTS
N <- Nodes
F <- Features

SPECIFICATION
SpecOpts

ACTION_CONSTRAINT
AtTermination

CONSTRAINT
AtTerminationDetected
================================================================================
