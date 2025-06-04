--------------------------- MODULE VoucherCancel ----------------------------

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
vtpCPrepared,

msgs

Messages ==

[type : {"Prepared"}, vh : H] \cup
[type : {"Prepared"}, vi : I] \cup
[type : {"Cancel", "Abort"}]

VTPTypeOK ==

/\ vState \in [V -> {"valid", "cancelled"}]
/\ vlcState \in [V -> {"working", "done"}]
/\ hState \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
/\ iState \in [I -> {"waiting", "prepared", "cancelled", "aborted"}]
/\ vtpState \in {"init", "done"}
/\ vtpCPrepared \subseteq (H \cup I)
/\ msgs \subseteq Messages

VTPInit ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ hState = [h \in H |-> "holding"]
/\ iState = [i \in I |-> "waiting"]
/\ vtpState = "init"
/\ vtpCPrepared   = {}
/\ msgs = {}
-----------------------------------------------------------------------------

VTPRcvPrepared(h,i) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ vtpState = "init"
/\ [type |-> "Prepared", vh |-> h] \in msgs
/\ [type |-> "Prepared", vi |-> i] \in msgs
/\ vtpCPrepared' = vtpCPrepared \cup {h,i}
/\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, msgs>>

VTPCancel(v) ==

/\ vState[v] = "valid"
/\ vlcState[v] = "working"
/\ vtpState = "init"
/\ vtpCPrepared = H \cup I
/\ vtpState' = "done"
/\ vState' = [vState EXCEPT ![v] = "cancelled"]
/\ vlcState' = [vlcState EXCEPT ![v] = "done"]
/\ msgs' = msgs \cup {[type |-> "Cancel"]}
/\ UNCHANGED <<hState, iState, vtpCPrepared>>

VTPAbort(v) ==

/\ vState[v] = "valid"
/\ vlcState[v] = "working"
/\ vtpState = "init"
/\ vtpState' = "done"
/\ msgs' = msgs \cup {[type |-> "Abort"]}
/\ UNCHANGED <<vState, vlcState, hState, iState, vtpCPrepared>>

HPrepare(h) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ hState[h] = "holding"
/\ hState' = [hState EXCEPT ![h] = "prepared"]
/\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
/\ UNCHANGED <<vState, vlcState, vtpState, iState, vtpCPrepared>>

HChooseToAbort(h) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ hState[h] = "holding"
/\ hState' = [hState EXCEPT ![h] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, iState, vtpCPrepared, msgs>>

HRcvCancelMsg(h) ==

/\ vState \in [V -> {"valid", "cancelled"}]
/\ vlcState \in [V -> {"working", "done"}]
/\ hState[h] = "holding"
/\ [type |-> "Cancel"] \in msgs
/\ hState' = [hState EXCEPT ![h] = "cancelled"]
/\ UNCHANGED <<vtpState, vState, vlcState, iState, vtpCPrepared, msgs>>

HRcvAbortMsg(h) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ hState[h] = "holding"
/\ [type |-> "Abort"] \in msgs
/\ hState' = [hState EXCEPT ![h] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, iState, vtpCPrepared, msgs>>

IPrepare(i) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ iState[i] = "waiting"
/\ iState' = [iState EXCEPT ![i] = "prepared"]
/\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
/\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpCPrepared>>

IChooseToAbort(i) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ iState[i] = "waiting"
/\ iState' = [iState EXCEPT ![i] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpCPrepared, msgs>>

IRcvCancelMsg(i) ==

/\ vState \in [V -> {"valid", "cancelled"}]
/\ vlcState \in [V -> {"working", "done"}]
/\ iState[i] = "waiting"
/\ [type |-> "Cancel"] \in msgs
/\ iState' = [iState EXCEPT ![i] = "cancelled"]
/\ UNCHANGED <<vtpState, vState, vlcState, hState, vtpCPrepared, msgs>>

IRcvAbortMsg(i) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ iState[i] = "waiting"
/\ [type |-> "Abort"] \in msgs
/\ iState' = [iState EXCEPT ![i] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpCPrepared, msgs>>

VTPNext ==
\/ \E v \in V:
VTPCancel(v) \/ VTPAbort(v)
\/ \E h,i \in H \cup I:
VTPRcvPrepared(h,i)
\/ \E h \in H:
HPrepare(h) \/ HChooseToAbort(h)
\/ HRcvAbortMsg(h) \/ HRcvCancelMsg(h)
\/ \E i \in I:
IPrepare(i) \/ IChooseToAbort(i)
\/ IRcvAbortMsg(i) \/ IRcvCancelMsg(i)
-----------------------------------------------------------------------------
VTPConsistent ==

/\ \A h \in H, i \in I :   /\ ~ /\ hState[h] = "cancelled"
/\ iState[i] = "aborted"
/\ ~ /\ hState[h] = "aborted"
/\ iState[i] = "cancelled"
-----------------------------------------------------------------------------
VTPVars == <<hState, iState, vState, vlcState, vtpState, vtpCPrepared, msgs>>

VTPSpec == VTPInit /\ [][VTPNext]_VTPVars

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------

INSTANCE VoucherLifeCycle

THEOREM VTPSpec => VSpec

=============================================================================
