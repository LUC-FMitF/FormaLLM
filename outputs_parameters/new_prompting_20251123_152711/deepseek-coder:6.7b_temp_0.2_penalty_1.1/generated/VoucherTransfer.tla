---- MODULE VoucherTransfer ----
EXTENDS ModuleName

CONSTANTS
  V = {v1, v2, v3}
  SH = {src1, src2, src3}
  DH = {dst1, dst2, dst3}

VARIABLES
  msgs <<>> : MsgSet
  vState[v] ==> VoucherState
  shState[sh] ==> HolderState
  dhState[dh] ==> HolderState

ASSIGN
  VTPSpec == (VTPTypeOK /\ VTPConsistent)
  VTPTypeOK == (FORALL v : Vouchers, VoucherLifeCycleSpec(v))
  VTPConsistent == 
    ((shState[src1] = PreparedForTransfer \/ shState[src2] = PreparedForTransfer \/ shState[src3] = PreparedForTransfer) /\
     (dhState[dst1] = WaitingForVoucher \/ dhState[dst2] = WaitingForVoucher \/ dhState[dst3] = WaitingForVoucher))
  MsgSet == Union {PreparedMsg(vsh, vdh)}
  PreparedMsg(vsh, vdh) == << (vsh, vdh) : Msg >>
====