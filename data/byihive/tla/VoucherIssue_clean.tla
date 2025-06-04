---------------------------- MODULE VoucherIssue ----------------------------

CONSTANT
V,
H,
I

VARIABLES
vState,
vlcState,

hState,
iState,
vtpState,
vtpIPrepared,

msgs

Messages ==

[type : {"Prepared"}, vi : I] \cup
[type : {"Prepared"}, vh : H] \cup
[type : {"Issue", "Abort"}]

VTPTypeOK ==

/\ vState \in [V -> {"phantom", "valid"}]
/\ vlcState \in [V -> {"init", "working"}]
/\ hState \in [H -> {"waiting", "prepared", "holding", "aborted"}]
/\ iState \in [I -> {"waiting", "prepared", "issued", "aborted"}]
/\ vtpState \in {"init", "done"}
/\ vtpIPrepared \subseteq (H \cup I)
/\ msgs \subseteq Messages

VTPInit ==

/\ vState = [v \in V |-> "phantom"]
/\ vlcState = [v \in V |-> "init"]
/\ hState = [h \in H |-> "waiting"]
/\ iState = [i \in I |-> "waiting"]
/\ vtpState = "init"
/\ vtpIPrepared   = {}
/\ msgs = {}
-----------------------------------------------------------------------------

VTPRcvPrepared(h,i) ==

/\ vState = [v \in V |-> "phantom"]
/\ vlcState = [v \in V |-> "init"]
/\ vtpState = "init"
/\ [type |-> "Prepared", vh |-> h] \in msgs
/\ [type |-> "Prepared", vi |-> i] \in msgs
/\ vtpIPrepared' = vtpIPrepared \cup {h,i}
/\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, msgs>>

VTPIssue(v) ==

/\ vState[v] = "phantom"
/\ vlcState[v] = "init"
/\ vtpState = "init"
/\ vtpIPrepared = H \cup I
/\ vtpState' = "done"
/\ vState' = [vState EXCEPT ![v] = "valid"]
/\ vlcState' = [vlcState EXCEPT ![v] = "working"]
/\ msgs' = msgs \cup {[type |-> "Issue"]}
/\ UNCHANGED <<hState, iState, vtpIPrepared>>

VTPAbort(v) ==

/\ vState[v] = "phantom"
/\ vlcState[v] = "init"
/\ vtpState = "init"
/\ vtpState' = "done"
/\ msgs' = msgs \cup {[type |-> "Abort"]}
/\ UNCHANGED <<vState, vlcState, hState, iState, vtpIPrepared>>

HPrepare(h) ==

/\ vState = [v \in V |-> "phantom"]
/\ vlcState = [v \in V |-> "init"]
/\ hState[h] = "waiting"
/\ hState' = [hState EXCEPT ![h] = "prepared"]
/\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
/\ UNCHANGED <<vState, vlcState, vtpState, iState, vtpIPrepared>>

HChooseToAbort(h) ==

/\ vState = [v \in V |-> "phantom"]
/\ vlcState = [v \in V |-> "init"]
/\ hState[h] = "waiting"
/\ hState' = [hState EXCEPT ![h] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, iState, vtpIPrepared, msgs>>

HRcvIssueMsg(h) ==

/\ vState \in [V -> {"phantom", "valid"}]
/\ vlcState \in [V -> {"init", "working"}]
/\ hState[h] = "waiting"
/\ [type |-> "Issue"] \in msgs
/\ hState' = [hState EXCEPT ![h] = "holding"]
/\ UNCHANGED <<vtpState, vState, vlcState, iState, vtpIPrepared, msgs>>

HRcvAbortMsg(h) ==

/\ vState = [v \in V |-> "phantom"]
/\ vlcState = [v \in V |-> "init"]
/\ hState[h] = "waiting"
/\ [type |-> "Abort"] \in msgs
/\ hState' = [hState EXCEPT ![h] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, iState, vtpIPrepared, msgs>>

IPrepare(i) ==

/\ vState = [v \in V |-> "phantom"]
/\ vlcState = [v \in V |-> "init"]
/\ iState[i] = "waiting"
/\ iState' = [iState EXCEPT ![i] = "prepared"]
/\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
/\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpIPrepared>>

IChooseToAbort(i) ==

/\ vState = [v \in V |-> "phantom"]
/\ vlcState = [v \in V |-> "init"]
/\ iState[i] = "waiting"
/\ iState' = [iState EXCEPT ![i] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpIPrepared, msgs>>

IRcvIssueMsg(i) ==

/\ vState \in [V -> {"phantom", "valid"}]
/\ vlcState \in [V -> {"init", "working"}]
/\ iState[i] = "waiting"
/\ [type |-> "Issue"] \in msgs
/\ iState' = [iState EXCEPT ![i] = "issued"]
/\ UNCHANGED <<vtpState, vState, vlcState, hState, vtpIPrepared, msgs>>

IRcvAbortMsg(i) ==

/\ vState = [v \in V |-> "phantom"]
/\ vlcState = [v \in V |-> "init"]
/\ iState[i] = "waiting"
/\ [type |-> "Abort"] \in msgs
/\ iState' = [iState EXCEPT ![i] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpIPrepared, msgs>>

VTPNext ==
\/ \E v \in V:
VTPIssue(v) \/ VTPAbort(v)
\/ \E h,i \in H \cup I:
VTPRcvPrepared(h,i)
\/ \E h \in H:
HPrepare(h) \/ HChooseToAbort(h)
\/ HRcvAbortMsg(h) \/ HRcvIssueMsg(h)
\/ \E i \in I:
IPrepare(i) \/ IChooseToAbort(i)
\/ IRcvAbortMsg(i) \/ IRcvIssueMsg(i)
-----------------------------------------------------------------------------
VTPConsistent ==

/\ \A h \in H, i \in I :   /\ ~ /\ hState[h] = "holding"
/\ iState[i] = "aborted"
/\ ~ /\ hState[h] = "aborted"
/\ iState[i] = "issued"
-----------------------------------------------------------------------------
VTPVars == <<hState, iState, vState, vlcState, vtpState, vtpIPrepared, msgs>>

VTPSpec == VTPInit /\ [][VTPNext]_VTPVars

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------

INSTANCE VoucherLifeCycle

THEOREM VTPSpec => VSpec

=============================================================================
