---- MODULE VoucherTransfer ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANTS
  V = {v1, v2, v3}
  SH = {src1, src2, src3}
  DH = {dst1, dst2, dst3}

VARIABLES
  msgs <<>> /\ vState[v] \in V ~~ shState[sh] \in SH ~~ dhState[dh] \in DH

ASSUME
  -- Assumptions about the existence of vouchers, source/destination voucher holders and two-phase commit protocol go here.

DEFINE
  IsPrepared(v) == EXISTS {sh | shState[s] = v}
  IsAborted()    == EXISTS {dh, sh | dhState[d] \in DH /\ shState[s] \in SH /\ msgs[{dh, sh}] = AbortMsg}

-- Operations of the Voucher Transaction Provider (VTP)
OPERATIONS
  Prepare() == IF IsPrepared(v) THEN Skip 
              ELSE Send(PreparedMsg(shState[s], v)) /\ msgs := msgs \cup {PreparedMsg(shState[s], v)} END
  Abort()   == IF IsAborted()   THEN Skip
              ELSE Send(AbortMsg) /\ msgs := msgs \cup {AbortMsg} END
  Transfer() == IF EXISTS {dh, sh | dhState[d] = dst /\ shState[s] = src /\ IsPrepared(v)} THEN Skip
              ELSE Send(TransferMsg(shState[s], v)) /\ msgs := msgs \cup {TransferMsg(shState[s], v)} END

-- State predicates for Voucher Transaction Provider (VTP)
PREDICATE
  VTPTypeOK() == INTERSECT (vState[v] : v \in V), (shState[s] : s \in SH /\ dhState[d] : d \in DH) = {}
  VTPConsistent() == EXISTS {dh, sh | dhState[d] = dst /\ shState[s] = src} IMPLIES IsPrepared(v)
====