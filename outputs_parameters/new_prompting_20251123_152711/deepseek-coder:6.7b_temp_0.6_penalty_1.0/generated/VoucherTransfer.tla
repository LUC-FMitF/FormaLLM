---- MODULE VoucherTransfer ----
EXTENDS VoucherLifeCycle

\* The set of Vouchers
V == {v1, v2, v3}

\* The set of "Source" Voucher Holders
SH == {src1, src2, src3}

\* The set of "Destination" Voucher Holders
DH == {dst1, dst2, dst3}

\* vState[v] is the state of voucher v
vState(v) == \E x \in V . v = x

\* vlcState[v] is the state of the voucher life cycle
vlcState(v) == \E x \in V . v = x

\* machine.
machine == \E x \in MACHINE . x

\* shState[sh] is the state of "source" voucher holder sh
shState(sh) == \E x \in SH . sh = x

\* dhState[dh] is the state of "destination" voucher holder dh
dhState(dh) == \E x \in DH . dh = x

\* The state of the voucher transaction provider.
VTPState == \E x \in VTP . x

\* The set of SHs and DHs from which the VTP has received
\* "Prepared for Voucher Transfer" messages.
vtpTPrepared == {sh | sh \in SH} \union {dh | dh \in DH}

\* The set of all possible messages.
msgs == {msg | msg \in MSG}

\* The set of all possible messages.
MSG == {msgPrepared | msgPrepared \in PreparedMsg}

\* The set of all possible "Prepared" messages.
PreparedMsg == {msg | \E sh \in SH, dh \in DH . msg = <vsh = sh, vdh = dh>}

\* The set of all possible "Transfer" messages.
TransferMsg == {msg | \E sh \in SH, dh \in DH . msg = <vsh = sh, vdh = dh>}

\* The set of all possible "Abort" messages.
AbortMsg == {msg | \E sh \in SH, dh \in DH . msg = <vsh = sh, vdh = dh>}

\* Type-correctness invariant
VTPTypeOK == \A sh \in SH, dh \in DH . sh \in vtpTPrepared \Rightarrow shState(sh) = Prepared

\* Consistency invariant
VTPConsistent == \A sh \in SH, dh \in DH . dh \in vtpTPrepared \Rightarrow dhState(dh) = Prepared

\* The complete spec of the a Voucher Transfer using Two-Phase Commit protocol.
VTPSpec == VTPTypeOK /\ VTPConsistent

\* Assert that the Voucher Transfer specification implements the Voucher life cycle specification.
IMPLEMENTS == VTPSpec == VSpec
====