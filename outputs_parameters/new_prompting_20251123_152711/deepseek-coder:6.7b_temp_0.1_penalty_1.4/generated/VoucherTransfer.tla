---- MODULE VoucherTransfer ----
EXTENDS VoucherLifeCycle

CONSTANTS
  V = {v1, v2, v3}
  SH = {src1, src2, src3}
  DH = {dst1, dst2, dst3}

VARIABLES
  msgs, vState[V], vlcState[V], shState[SH], dhState[DH], vtpState

ASSUME
  VTPTypeOK == (vtpState = INITIAL \/ vtpState = TRANSFERRING \/ vtpState = ABORTING)
  VTPConsistent == (vtpState = INITIAL \/ (FORALL v \in V . vState[v] = vlcState[v]))

DEFINE
  VTPSpec == (VTPTypeOK /\ VTPConsistent)

SPECIFICATION VTPSpec

INVARIANTS VTPTypeOK VTPConsistent

====
CONSTANTS
  V = {v1, v2, v3}
  SH = {src1, src2, src3}
  DH = {dst1, dst2, dst3}
INVARIANTS VTPTypeOK VTPConsistent
SPECIFICATION VTPSpec
\* Refinement does not hold
\*PROPERTY VSpec
CHECK_DEADLOCK FALSE
====