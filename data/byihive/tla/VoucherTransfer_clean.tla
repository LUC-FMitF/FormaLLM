-------------------------- MODULE VoucherTransfer --------------------------

CONSTANT
V,
SH,
DH

VARIABLES
vState,
vlcState,

shState,
dhState,
vtpState,
vtpTPrepared,

msgs

Messages ==

[type : {"Prepared"}, vsh : SH] \cup
[type : {"Prepared"}, vdh : DH] \cup
[type : {"Transfer", "Abort"}]

VTPTypeOK ==

/\ vState \in [V -> {"valid"}]
/\ vlcState \in [V -> {"working"}]
/\ shState \in [SH -> {"holding", "prepared", "transferred", "aborted"}]
/\ dhState \in [DH -> {"waiting", "prepared", "holding", "aborted"}]
/\ vtpState \in {"init", "done"}
/\ vtpTPrepared \subseteq (SH \cup DH)
/\ msgs \subseteq Messages

VTPInit ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ shState = [sh \in SH |-> "holding"]
/\ dhState = [dh \in DH |-> "waiting"]
/\ vtpState = "init"
/\ vtpTPrepared   = {}
/\ msgs = {}
-----------------------------------------------------------------------------

VTPRcvPrepared(sh,dh) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ vtpState = "init"
/\ [type |-> "Prepared", vsh |-> sh] \in msgs
/\ [type |-> "Prepared", vdh |-> dh] \in msgs
/\ vtpTPrepared' = vtpTPrepared \cup {sh,dh}
/\ UNCHANGED <<vState, vlcState, shState, dhState, vtpState, msgs>>

VTPTransfer(v) ==

/\ vState[v] = "valid"
/\ vlcState[v] = "working"
/\ vtpState = "init"
/\ vtpTPrepared = SH \cup DH
/\ vtpState' = "done"
/\ msgs' = msgs \cup {[type |-> "Transfer"]}
/\ UNCHANGED <<shState, dhState, vState, vlcState, vtpTPrepared>>

VTPAbort(v) ==

/\ vState[v] = "valid"
/\ vlcState[v] = "working"
/\ vtpState = "init"
/\ vtpState' = "done"
/\ msgs' = msgs \cup {[type |-> "Abort"]}
/\ UNCHANGED <<vState, vlcState, shState, dhState, vtpTPrepared>>

SHPrepare(sh) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ shState[sh] = "holding"
/\ shState' = [shState EXCEPT ![sh] = "prepared"]
/\ msgs' = msgs \cup {[type |-> "Prepared", vsh |-> sh]}
/\ UNCHANGED <<vState, vlcState, vtpState, dhState, vtpTPrepared>>

SHChooseToAbort(sh) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ shState[sh] = "holding"
/\ shState' = [shState EXCEPT ![sh] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, dhState, vtpTPrepared, msgs>>

SHRcvTransferMsg(sh) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ shState[sh] = "holding"
/\ [type |-> "Transfer"] \in msgs
/\ shState' = [shState EXCEPT ![sh] = "transferred"]
/\ UNCHANGED <<vtpState, vlcState, vState, dhState, vtpTPrepared, msgs>>

SHRcvAbortMsg(sh) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ shState[sh] = "holding"
/\ [type |-> "Abort"] \in msgs
/\ shState' = [shState EXCEPT ![sh] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, dhState, vtpTPrepared, msgs>>

DHPrepare(dh) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ dhState[dh] = "waiting"
/\ dhState' = [dhState EXCEPT ![dh] = "prepared"]
/\ msgs' = msgs \cup {[type |-> "Prepared", vdh |-> dh]}
/\ UNCHANGED <<vState, vlcState, vtpState, shState, vtpTPrepared>>

DHChooseToAbort(dh) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ dhState[dh] = "waiting"
/\ dhState' = [dhState EXCEPT ![dh] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, shState, vtpTPrepared, msgs>>

DHRcvTransferMsg(dh) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ dhState[dh] = "waiting"
/\ [type |-> "Transfer"] \in msgs
/\ dhState' = [dhState EXCEPT ![dh] = "holding"]
/\ UNCHANGED <<vtpState, vState, vlcState, shState, vtpTPrepared, msgs>>

DHRcvAbortMsg(dh) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ dhState[dh] = "waiting"
/\ [type |-> "Abort"] \in msgs
/\ dhState' = [dhState EXCEPT ![dh] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, shState, vtpTPrepared, msgs>>

VTPNext ==
\/ \E v \in V:
VTPTransfer(v) \/ VTPAbort(v)
\/ \E sh,dh \in SH \cup DH:
VTPRcvPrepared(sh,dh)
\/ \E sh \in SH:
SHPrepare(sh) \/ SHChooseToAbort(sh)
\/ SHRcvAbortMsg(sh) \/ SHRcvTransferMsg(sh)
\/ \E dh \in DH:
DHPrepare(dh) \/ DHChooseToAbort(dh)
\/ DHRcvAbortMsg(dh) \/ DHRcvTransferMsg(dh)
-----------------------------------------------------------------------------
VTPConsistent ==

/\ \A sh \in SH, dh \in DH :   /\ ~ /\ shState[sh] = "transferred"
/\ dhState[dh] = "aborted"
/\ ~ /\ shState[sh] = "aborted"
/\ dhState[dh] = "holding"
-----------------------------------------------------------------------------
VTPVars == <<shState, dhState, vState, vlcState, vtpState, vtpTPrepared, msgs>>

VTPSpec == VTPInit /\ [][VTPNext]_VTPVars

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------

INSTANCE VoucherLifeCycle

THEOREM VTPSpec => VSpec

=============================================================================
