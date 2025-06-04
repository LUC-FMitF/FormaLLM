--------------------------- MODULE VoucherRedeem ----------------------------

CONSTANT
V,
H,
C

VARIABLES
vState,
vlcState,

hState,
cState,
vtpState,
vtpRPrepared,

msgs

Messages ==

[type : {"Prepared"}, vh : H] \cup
[type : {"Prepared"}, vc : C] \cup
[type : {"Redeem", "Abort"}]

VTPTypeOK ==

/\ vState \in [V -> {"valid", "redeemed"}]
/\ vlcState \in [V -> {"working", "done"}]
/\ hState \in [H -> {"holding", "prepared", "redeemed", "aborted"}]
/\ cState \in [C -> {"waiting", "prepared", "redeemed", "aborted"}]
/\ vtpState \in {"init", "done"}
/\ vtpRPrepared \subseteq (H \cup C)
/\ msgs \subseteq Messages

VTPInit ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ hState = [h \in H |-> "holding"]
/\ cState = [c \in C |-> "waiting"]
/\ vtpState = "init"
/\ vtpRPrepared   = {}
/\ msgs = {}
-----------------------------------------------------------------------------

VTPRcvPrepared(h,c) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ vtpState = "init"
/\ [type |-> "Prepared", vh |-> h] \in msgs
/\ [type |-> "Prepared", vc |-> c] \in msgs
/\ vtpRPrepared' = vtpRPrepared \cup {h,c}
/\ UNCHANGED <<vState, vlcState, hState, cState, vtpState, msgs>>

VTPRedeem(v) ==

/\ vState[v] = "valid"
/\ vlcState[v] = "working"
/\ vtpState = "init"
/\ vtpRPrepared = H \cup C
/\ vtpState' = "done"
/\ vState' = [vState EXCEPT ![v] = "redeemed"]
/\ vlcState' = [vlcState EXCEPT ![v] = "done"]
/\ msgs' = msgs \cup {[type |-> "Redeem"]}
/\ UNCHANGED <<hState, cState, vtpRPrepared>>

VTPAbort(v) ==

/\ vState[v] = "valid"
/\ vlcState[v] = "working"
/\ vtpState = "init"
/\ vtpState' = "done"
/\ msgs' = msgs \cup {[type |-> "Abort"]}
/\ UNCHANGED <<vState, vlcState, hState, cState, vtpRPrepared>>

HPrepare(h) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ hState[h] = "holding"
/\ hState' = [hState EXCEPT ![h] = "prepared"]
/\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
/\ UNCHANGED <<vState, vlcState, vtpState, cState, vtpRPrepared>>

HChooseToAbort(h) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ hState[h] = "holding"
/\ hState' = [hState EXCEPT ![h] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, cState, vtpRPrepared, msgs>>

HRcvRedeemMsg(h) ==

/\ vState \in [V -> {"valid", "redeemed"}]
/\ vlcState \in [V -> {"working", "done"}]
/\ hState[h] = "holding"
/\ [type |-> "Redeem"] \in msgs
/\ hState' = [hState EXCEPT ![h] = "redeemed"]
/\ UNCHANGED <<vtpState, vState, vlcState, cState, vtpRPrepared, msgs>>

HRcvAbortMsg(h) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ hState[h] = "holding"
/\ [type |-> "Abort"] \in msgs
/\ hState' = [hState EXCEPT ![h] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, cState, vtpRPrepared, msgs>>

CPrepare(c) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ cState[c] = "waiting"
/\ cState' = [cState EXCEPT ![c] = "prepared"]
/\ msgs' = msgs \cup {[type |-> "Prepared", vc |-> c]}
/\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpRPrepared>>

CChooseToAbort(c) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ cState[c] = "waiting"
/\ cState' = [cState EXCEPT ![c] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpRPrepared, msgs>>

CRcvRedeemMsg(c) ==

/\ vState \in [V -> {"valid", "redeemed"}]
/\ vlcState \in [V -> {"working", "done"}]
/\ cState[c] = "waiting"
/\ [type |-> "Redeem"] \in msgs
/\ cState' = [cState EXCEPT ![c] = "redeemed"]
/\ UNCHANGED <<vtpState, vState, vlcState, hState, vtpRPrepared, msgs>>

CRcvAbortMsg(c) ==

/\ vState = [v \in V |-> "valid"]
/\ vlcState = [v \in V |-> "working"]
/\ cState[c] = "waiting"
/\ [type |-> "Abort"] \in msgs
/\ cState' = [cState EXCEPT ![c] = "aborted"]
/\ UNCHANGED <<vState, vlcState, vtpState, hState, vtpRPrepared, msgs>>

VTPNext ==
\/ \E v \in V:
VTPRedeem(v) \/ VTPAbort(v)
\/ \E h,c \in H \cup C:
VTPRcvPrepared(h,c)
\/ \E h \in H:
HPrepare(h) \/ HChooseToAbort(h)
\/ HRcvAbortMsg(h) \/ HRcvRedeemMsg(h)
\/ \E c \in C:
CPrepare(c) \/ CChooseToAbort(c)
\/ CRcvAbortMsg(c) \/ CRcvRedeemMsg(c)
-----------------------------------------------------------------------------
VTPConsistent ==

/\ \A h \in H, c \in C :   /\ ~ /\ hState[h] = "redeemed"
/\ cState[c] = "aborted"
/\ ~ /\ hState[h] = "aborted"
/\ cState[c] = "redeemed"
-----------------------------------------------------------------------------
VTPVars == <<hState, cState, vState, vlcState, vtpState, vtpRPrepared, msgs>>

VTPSpec == VTPInit /\ [][VTPNext]_VTPVars

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------

INSTANCE VoucherLifeCycle

THEOREM VTPSpec => VSpec

=============================================================================
