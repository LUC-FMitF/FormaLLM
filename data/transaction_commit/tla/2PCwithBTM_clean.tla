----------------------------- MODULE 2PCwithBTM ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT RM,
RMMAYFAIL,
TMMAYFAIL

VARIABLES rmState, tmState, pc

canCommit ==    \A rmc \in RM: rmState[rmc] \in {"prepared"}
\/ \E rm \in RM : rmState[rm] \in {"committed"}
canAbort ==     \E rm \in RM : rmState[rm] \in {"aborted","failed"}
/\ ~\E rmc \in RM : rmState[rmc]= "committed"

vars == << rmState, tmState, pc >>

ProcSet == (RM) \cup {0} \cup {10}

Init ==
/\ rmState = [rm \in RM |-> "working"]
/\ tmState = "init"
/\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
[] self = 0 -> "TS"
[] self = 10 -> "BTS"]

RS(self) == /\ pc[self] = "RS"
/\ IF rmState[self] \in {"working", "prepared"}
THEN /\ \/ /\ rmState[self] = "working"
/\ rmState' = [rmState EXCEPT ![self] = "prepared"]
\/ /\ \/ /\ tmState="commit"
/\ rmState' = [rmState EXCEPT ![self] = "committed"]
\/ /\ rmState[self]="working" \/ tmState="abort"
/\ rmState' = [rmState EXCEPT ![self] = "aborted"]
\/ /\ IF RMMAYFAIL /\ ~\E rm \in RM:rmState[rm]="failed"
THEN /\ rmState' = [rmState EXCEPT ![self] = "failed"]
ELSE /\ TRUE
/\ UNCHANGED rmState
/\ pc' = [pc EXCEPT ![self] = "RS"]
ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
/\ UNCHANGED rmState
/\ UNCHANGED tmState

RManager(self) == RS(self)

TS == /\ pc[0] = "TS"
/\ \/ /\ canCommit
/\ pc' = [pc EXCEPT ![0] = "TC"]
\/ /\ canAbort
/\ pc' = [pc EXCEPT ![0] = "TA"]
/\ UNCHANGED << rmState, tmState >>

TC == /\ pc[0] = "TC"
/\ tmState' = "commit"
/\ pc' = [pc EXCEPT ![0] = "F1"]
/\ UNCHANGED rmState

F1 == /\ pc[0] = "F1"
/\ IF TMMAYFAIL
THEN /\ tmState' = "hidden"
ELSE /\ TRUE
/\ UNCHANGED tmState
/\ pc' = [pc EXCEPT ![0] = "Done"]
/\ UNCHANGED rmState

TA == /\ pc[0] = "TA"
/\ tmState' = "abort"
/\ pc' = [pc EXCEPT ![0] = "F2"]
/\ UNCHANGED rmState

F2 == /\ pc[0] = "F2"
/\ IF TMMAYFAIL
THEN /\ tmState' = "hidden"
ELSE /\ TRUE
/\ UNCHANGED tmState
/\ pc' = [pc EXCEPT ![0] = "Done"]
/\ UNCHANGED rmState

TManager == TS \/ TC \/ F1 \/ TA \/ F2

BTS == /\ pc[10] = "BTS"
/\ \/ /\ canCommit /\ tmState="hidden"
/\ pc' = [pc EXCEPT ![10] = "BTC"]
\/ /\ canAbort /\ tmState="hidden"
/\ pc' = [pc EXCEPT ![10] = "BTA"]
/\ UNCHANGED << rmState, tmState >>

BTC == /\ pc[10] = "BTC"
/\ tmState' = "commit"
/\ pc' = [pc EXCEPT ![10] = "Done"]
/\ UNCHANGED rmState

BTA == /\ pc[10] = "BTA"
/\ tmState' = "abort"
/\ pc' = [pc EXCEPT ![10] = "Done"]
/\ UNCHANGED rmState

BTManager == BTS \/ BTC \/ BTA

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
/\ UNCHANGED vars

Next == TManager \/ BTManager
\/ (\E self \in RM: RManager(self))
\/ Terminating

Spec == /\ Init /\ [][Next]_vars
/\ \A self \in RM : WF_vars(RManager(self))
/\ WF_vars(TManager)
/\ WF_vars(BTManager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

TypeOK ==

/\ rmState \in [RM -> {"working", "prepared", "committed", "aborted", "failed"}]
/\ tmState \in {"init", "commit", "abort", "hidden"}

Consistency ==

\A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
/\ rmState[rm2] = "committed"

NotCommitted == \A rm \in RM : rmState[rm] # "committed"

=============================================================================
