------------------------------- MODULE EWD998_opts -------------------------------
EXTENDS EWD998, TLC, IOUtils, CSV, Randomization

ASSUME TLCGet("config").mode = "generate"

ASSUME TLCGet("config").depth = -1

ASSUME TLCGet("config").deadlock = FALSE

ASSUME TLCGet("revision").timestamp >= 1663391404

--------------------------------------------------------------------------------

FeatureFlags ==
{"pt1","pt2","pt3","pt4","pt5"}

CONSTANT F
ASSUME F \subseteq FeatureFlags

--------------------------------------------------------------------------------

InitSim ==

/\ active \in RandomSubset(1000, [Node -> BOOLEAN])
/\ color \in RandomSubset(1000, [Node -> Color])

InitiateProbeOpts ==
/\ IF "pt5" \in F THEN ~ active[0] ELSE TRUE
/\ InitiateProbe

PassTokenOpts(i) ==
/\ token.pos = i
/\ \/ ~ active[i]
\/ /\ "pt1" \in F
/\ color[i] = "black"
\/ /\ "pt2" \in F
/\ token.color = "black"
/\ token' = [token EXCEPT !.pos = CASE "pt3" \in F /\ color[i] = "black" -> 0
[] "pt4" \in F /\ token.color = "black" -> 0
[] OTHER    ->  @ - 1,
!.q = @ + counter[i],
!.color = IF color[i] = "black" THEN "black" ELSE @]
/\ color' = [ color EXCEPT ![i] = "white" ]
/\ UNCHANGED <<active, counter, pending>>

SystemOpts ==
\/ InitiateProbeOpts
\/ \E i \in Node \ {0}: PassTokenOpts(i)

SendMsgOpts(i) ==

/\ RandomElement(1..TLCGet("level")) = 1
/\ SendMsg(i)

EnvironmentOpts ==
\E i \in Node : SendMsgOpts(i) \/ RecvMsg(i) \/ Deactivate(i)

SpecOpts ==
InitSim /\ Init /\ [][SystemOpts \/ EnvironmentOpts]_vars

terminated ==
\A n \in Node: ~active[n] /\ pending[n] = 0

--------------------------------------------------------------------------------

ASSUME TLCSet(1, 0)

AtTermination ==

IF terminated # terminated'
THEN TLCSet(1, TLCGet("level"))
ELSE TRUE

AtTerminationDetected ==

terminationDetected =>
/\ LET o == TLCGet("stats").behavior.actions
IN
/\ Assert(o["InitiateProbeOpts"] + o["PassTokenOpts"] + o["SendMsgOpts"] + o["RecvMsg"] +
o["Deactivate"] = TLCGet("level") - 1, "Inconsistent action stats!")
/\ Assert(TLCGet("level") >= TLCGet(1), "Detection follows termination!")

/\ CSVWrite("%1$s#%2$s#%3$s#%4$s#%5$s#%6$s#%7$s#%8$s#%9$s#%10$s",
<< F, N, TLCGet("level"), TLCGet(1), TLCGet("level") - TLCGet(1),
o["InitiateProbeOpts"],o["PassTokenOpts"],
o["SendMsgOpts"],o["RecvMsg"],o["Deactivate"] >>,
IOEnv.Out)

/\ TLCSet(1, 0)

--------------------------------------------------------------------------------

Features ==
CHOOSE s \in SUBSET FeatureFlags : ToString(s) = IOEnv.F

Nodes ==
CHOOSE n \in 1..512 : ToString(n) = IOEnv.N

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
