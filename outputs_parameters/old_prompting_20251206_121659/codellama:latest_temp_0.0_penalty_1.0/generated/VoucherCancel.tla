---- MODULE VoucherCancel ----
EXTENDS VoucherLifeCycle
CONSTANTS
  V = {v1, v2, v3}
  H = {holder1, holder2, holder3}
  I = {issuer1, issuer2, issuer3}
INVARIANTS VTPTypeOK VTPConsistent
SPECIFICATION VTPSpec

Init ==
  VTPInit /\
  VTPConsistent /\
  VTPTypeOK /\
  VTPSpec

Next ==
  VTPNext /\
  VTPConsistent /\
  VTPTypeOK /\
  VTPSpec

VTPTypeOK ==
  \E v \in V : vState[v] = VTP

VTPConsistent ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPSpec ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPInit ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPNext ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPPrepare ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPCancel ==
  \E v \in V : vState[v] = VTP
  \E h \in H : hState[h] = VTP
  \E i \in I : iState[i] = VTP

VTPAbort ==
  \E v \in V : vState[v] = VTP
====