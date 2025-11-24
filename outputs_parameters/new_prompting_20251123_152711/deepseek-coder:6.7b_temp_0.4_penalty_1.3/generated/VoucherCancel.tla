---- MODULE VoucherCancel ----
EXTENDS VoucherLifeCycle
(***************************************************************************)
(* This specification describes the cancellation of Voucher between an      *)
(* Issuer and a Holder. It is implemented over the Two-Phase Commit         *)
(* protocol, in which a Voucher Transaction Provider (VTP) coordinates the  *)
(* Voucher Issuers (Is) to cancel vouchers (Vs) to Voucher Holders (Hs) as  *)
(* described in the VoucherLifeCycle specification module.                  *)
(***************************************************************************)

CONSTANTS
  H = {holder1, holder2, holder3}
  I = {issuer1, issuer2, issuer3}
  V = {v1, v2, v3}
VARIABLES
  msgs <<>> ==> MSG({Prepared}, (H \ UNION I) * V)
  vtpCPrepared == {}

ASSIGN
  (* The VTP receives a "Prepared" message from Voucher Holder h and the    *)
  (* Voucher Issuer i.                                                       *)
  msgs' == CASE
            [] msg \in msgs /\ MSGNAME(msg) = "Prepared" -> msgs \ {msg}
            [] OTHER -> msgs
          ENDCASE
  vtpCPrepared' == CASE
                    [] msg \in msgs /\ MSGNAME(msg) = "Prepared" -> vtpCPrepared UNION {MSGTUPLE(msg)}
                    [] OTHER -> vtpCPrepared
                  ENDCASE

(* The VTP Cancels the voucher; enabled iff the VTP is in its             *)
(* initial state and every H and I has sent a "Prepared" message.         *)
VTPTypeOK == LET vtpState == (msgs = <<>> /\ vtpCPrepared = {}) IN
                 vtpState /\ ALL h \in H : MsgTo(h, VTPSpec) /\ 
                                          ALL i \in I : MsgTo(i, VTPSpec)
               ENDLET

(* A state predicate asserting that a H and an I have not reached         *)
(* conflicting decisions. It is an invariant of the specification.        *)
VTPConsistent == LET vtpState == (msgs = <<>> /\ vtpCPrepared = {}) IN
                    ALL h \in H, i \in I : ~(MsgTo(h, VTPSpec) /\ MsgTo(i, VTPSpec))
                  ENDLET

(* The complete spec of the a Voucher Cancel using Two-Phase Commit       *)
(* protocol.                                                              *)
VTPSpec == EXTENDS VoucherLifeCycle.VSpec /\ VTPTypeOK /\ VTPConsistent
====