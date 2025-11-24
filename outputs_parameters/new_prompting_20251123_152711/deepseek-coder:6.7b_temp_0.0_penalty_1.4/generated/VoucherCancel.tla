---- MODULE VoucherCancel  ----
EXTENDS FiniteSets, Naturals, Sequences, VoucherLifeCycle
CONSTANTS V, H, I
VARIABLES msgs, vState[V], hState[H], iState[I]

(* The set of Vouchers *)
Vouchers == {v |-> (vState[v] \in {PreparedByHolder, PreparedByIssuer})}

(* The set of Voucher Holders *)
VoucherHolders == DOMAIN hState

(* The set of Voucher Issuers *)
VoucherIssuers == DOMAIN iState

(* vlcState[v] is the state of the voucher life cycle machine. *)
vlcState[v] == IFEXISTS x \in Vouchers : vState[x] = PreparedByHolder THEN hState[x] ELSE iState[x]

(* The set of Hs and Is from which the VTP has received "Prepared for Voucher Cancel" messages. *)
VTPReceived == UNION {h :-> vlcState[v] = PreparedByHolder FORALL v \in V} UNION {i :-> vlcState[v] = PreparedByIssuer FORALL v \in V}

(* The state of the voucher transaction provider. *)
VTPState == IFEXISTS x \in (DOMAIN hState) /\ EXISTS y \in (DOMAIN iState) : x = y THEN Abort ELSE Cancel

Init == 
  (* Initial predicate *)
  msgs = {} 
  AND vState[v] = New FORALL v \in V
  AND hState[h] = PreparedByHolder FORALL h \in H
  AND iState[i] = PreparedByIssuer FORALL i \in I
  AND VTPReceived = {}

Next == 
  (* Actions that may be performed by the processes *)
  IFEXISTS x \in (DOMAIN hState) /\ EXISTS y \in (DOMAIN iState) : x = y THEN msgs' = UNION {h :-> Abort FORALL h \in H} UNION {i :-> Abort FORALL i \in I}
  ELSE IF VTPReceived = UNION {h :-> vlcState[v] = PreparedByHolder FORALL v \in V} UNION {i :-> vlcState[v] = PreparedByIssuer FORALL v \in V} THEN msgs' = UNION {h :-> Cancel FORALL h \in H} UNION {i :-> Cancel FORALL i \in I}
  ELSE msgs' = msgs

(* The type-correctness invariant *)
VTPTypeOK == 
  (* Voucher holder h prepares. *)
  IFEXISTS x \in (DOMAIN hState) /\ EXISTS y \in (DOMAIN iState) : x = y THEN vState[v]' = PreparedByHolder FORALL v \in V
  ELSE IF VTPReceived = UNION {h :-> vlcState[v] = PreparedByHolder FORALL v \in V} UNION {i :-> vlcState[v] = PreparedByIssuer FORALL v \in V} THEN vState[v]' = Canceled FORALL v \in V
  (* Voucher issuer i prepares. *)
  AND IFEXISTS x \in (DOMAIN hState) /\ EXISTS y \in (DOMAIN iState) : x = y THEN vState[v]' = PreparedByIssuer FORALL v \in V
  ELSE IF VTPReceived = UNION {h :-> vlcState[v] = PreparedByHolder FORALL v \in V} UNION {i :-> vlcState[v] = PreparedByIssuer FORALL v \in V} THEN vState[v]' = Canceled FORALL v \in V
  (* A state predicate asserting that a H and an I have not reached conflicting decisions. *)
  AND IFEXISTS x \in (DOMAIN hState) /\ EXISTS y \in (DOMAIN iState) : x = y THEN hState[h]' = Decided FORALL h \in H
  ELSE IF VTPReceived = UNION {h :-> vlcState[v] = PreparedByHolder FORALL v \in V} UNION {i :-> vlcState[v] = PreparedByIssuer FORALL v \in V} THEN iState[i]' = Decided FORALL i \in I
  AND hState[h]' = IFEXISTS x \in (DOMAIN hState) /\ EXISTS y \in (DOMAIN iState) : x = y THEN PreparedByHolder ELSE hState[h]
  AND iState[i]' = IFEXISTS x \in (DOMAIN hState) /\ EXISTS y \in (DOMAIN iState) : x = y THEN PreparedByIssuer ELSE iState[i]

(* The complete spec of the a Voucher Cancel using Two-Phase Commit protocol. *)
VTPSpec == 
  (* The initial predicate *)
  Init 
  AND msgs' \in POWERSET (UNION {h :-> Abort FORALL h \in H} UNION {i :-> Abort FORALL i \in I})
  AND VTPTypeOK
====