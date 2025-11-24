---- MODULE VoucherCancel ----
EXTENDS VoucherLifeCycle

CONSTANTS
  V = {v1, v2, v3}
  H = {holder1, holder2, holder3}
  I = {issuer1, issuer2, issuer3}

VARIABLES
  vState[v] == {Prepared, Cancelled, Aborted}
  vlcState[v] == {Prepared, Cancelled, Aborted}
  hState[h] == {Prepared, Cancelled, Aborted}
  iState[i] == {Prepared, Cancelled, Aborted}
  vtpCPrepared == {h, i}
  msgs == {Prepared, Cancel, Abort}

ASSIGN
  VTPTypeOK == (vlcState[v] = Cancelled) /\ (hState[h] = Cancelled) /\ (iState[i] = Cancelled)
  VTPConsistent == (vState[v] = Cancelled) /\ (vlcState[v] = Cancelled)
  VTPSpec == (VTPTypeOK /\ VTPConsistent)

\* The initial predicate.
Init == (vState[v] = Prepared) /\ (vlcState[v] = Prepared) /\ (hState[h] = Prepared) /\ (iState[i] = Prepared)

\* The actions that may be performed by the processes.
NextState ==
  IF (vtpCPrepared = {h, i})
  THEN vState[v] = Cancelled
  ELSE vState[v] = Aborted

\* A state predicate asserting that a H and an I have not reached conflicting decisions.
NoConflict == (hState[h] /= Aborted) /\ (iState[i] /= Aborted)

\* The complete spec of the a Voucher Cancel using Two-Phase Commit protocol.
Spec == Init /\ NextState /\ NoConflict

=============================================================================
====
CONSTANTS
  V = {v1, v2, v3}
  H = {holder1, holder2, holder3}
  I = {issuer1, issuer2, issuer3}
INVARIANTS VTPTypeOK VTPConsistent
SPECIFICATION Spec
\*PROPERTY VSpec
CHECK_DEADLOCK FALSE
====