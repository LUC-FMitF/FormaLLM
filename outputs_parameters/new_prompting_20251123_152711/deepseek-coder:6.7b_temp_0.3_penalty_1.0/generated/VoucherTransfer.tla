---- MODULE VoucherTransfer ----
EXTENDS VoucherLifeCycle

(* Definitions *)
\* The set of Vouchers
Vouchers == V

\* The set of "Source" Voucher Holders
SHolders == SH

\* The set of "Destination" Voucher Holders
DHolders == DH

\* vState[v] is the state of voucher v.
vState[v] ==
  CASE v 
    IN v1 -> State1
    IN v2 -> State2
    IN v3 -> State3
  END

\* vlcState[v] is the state of the voucher life cycle
vlcState[v] ==
  CASE v 
    IN v1 -> v1State
    IN v2 -> v2State
    IN v3 -> v3State
  END

\* machine.
machine == VTP

\* shState[sh] is the state of "source" voucher holder sh.
shState[sh] ==
  CASE sh 
    IN src1 -> src1State
    IN src2 -> src2State
    IN src3 -> src3State
  END

\* dhState[dh] is the state of "destination" voucher holder dh.
dhState[dh] ==
  CASE dh 
    IN dst1 -> dst1State
    IN dst2 -> dst2State
    IN dst3 -> dst3State
  END

\* The state of the voucher transaction provider.
VTPState == machine

\* The set of SHs and DHs from which the VTP has received
"Prepared for Voucher Transfer" messages.
VTPPrepared == {sh |-> shState[sh] = Prepared} \/ {dh |-> dhState[dh] = Prepared}

(* Invariants *)
\* The set of all possible messages.
Messages == {"Prepared", "Transfer", "Abort"}

\* The type-correctness invariant
VTPTypeOK == (ALL sh, dh \in SHolders /\ dh \in DHolders : (shState[sh] = Prepared /\ dhState[dh] = Prepared) IMPLIES VTPState = VTP)

\* The consistency invariant
VTPConsistent == (ALL sh, dh \in SHolders /\ dh \in DHolders : (shState[sh] = Abort /\ dhState[dh] = Abort) IMPLIES VTPState = VTP)

(* Specification *)
VTPSpec == (VTPState = VTP /\ VTPPrepared = SHolders \/ DHolders) IMPLIES (VTPState = VTP /\ (ALL sh, dh \in SHolders /\ dh \in DHolders : shState[sh] = Transfer /\ dhState[dh] = Transfer))

(* Refinement does not hold *)
\*PROPERTY VSpec
CHECK_DEADLOCK FALSE

(* Assert that the Voucher Transfer specification implements the Voucher life cycle specification *)
\*THM VoucherTransferImplementsVoucherLifeCycle == VTPSpec SUBSET VSpec
====