---- MODULE VoucherCancel ----
(***************************************************************************)
(* This specification describes the cancellation of Voucher between an      *)
(* Issuer and a Holder. It is implemented over the Two-Phase Commit         *)
(* protocol, in which a Voucher Transaction Provider (VTP) coordinates the  *)
(* Voucher Issuers (Is) to cancel vouchers (Vs) to Voucher Holders (Hs) as  *)
(* described in the VoucherLifeCycle specification module. In this          *)
(* specification, Hs and Is spontaneously issue Prepared messages. We       *)
(* ignore the Prepare messages that the VTP can send to the Hs and Is.      *)
(***************************************************************************)

EXTENDS MODULE VoucherLifeCycle

CONSTANTS
  V  /\ IN V = {v1, v2, v3}
  H  /\ IN H = {holder1, holder2, holder3}
  I  /\ IN I = {issuer1, issuer2, issuer3}

VARIABLES
  msgs   /\ msgs \SUBSET (H x V) UNION (I x V)
  vState[v]  /\ vState[v] \IN {Prepared, Cancelled, Aborted}
  hState[h]  /\ hState[h] \IN {Prepared, DecidedAbort, ToldCancel}
  iState[i]  /\ iState[i] \IN {Prepared, DecidedAbort, ToldCancel}
  vtpCPrepared   /\ vtpCPrepared = H x I

(* The state of the voucher transaction provider. *)
PROCEDURE VTP(x) ==
  IF (hState[x] = Prepared AND iState[x] = Prepared)
    THEN vState[x] := Cancelled
    ELSEIF hState[x] = DecidedAbort OR iState[x] = DecidedAbort
      THEN vState[x] := Aborted
  ENDIF

(* The set of Hs and Is from which the VTP has received "Prepared for Voucher Cancel" messages. *)
PROCEDURE Prepare(h, i) ==
  IF (vtpCPrepared \SUBSET {h x I} UNION {i x H})
    THEN msgs := msgs U {h x V} U {i x V}
  ENDIF

(* The type-correctness invariant *)
INVARIANT VTPTypeOK ==
  EVERY h IN H, v IN V: (vState[v] = Cancelled IFF (hState[h] = ToldCancel AND iState[SELECT i : i IN I | v IN V[i]] = ToldCancel))

(* The initial predicate. *)
INITIAL ==
  msgs := {}
  vState := [v \in V |-> Prepared]
  hState, iState := [x \in H U I |-> Prepared]

(* A state predicate asserting that a H and an I have not reached conflicting decisions. *)
INVARIANT VTPConsistent ==
  EVERY h IN H, i IN I: (vState[SELECT v : v IN V | vtpCPrepared = {h x i}] = Cancelled OR vState[SELECT v : v IN V | vtpCPrepared = {i x h}] = Aborted)

(* The complete spec of the a Voucher Cancel using Two-Phase Commit protocol. *)
SPECIFICATION VTPSpec ==
  EVENTUALLY EXISTS h, i: (hState[h] = DecidedAbort AND iState[i] = DecidedAbort)
=============================================================================
====