---- MODULE VoucherCancel ----
EXTENDS ModuleName
(***************************************************************************)
(* This specification describes the cancellation of Voucher between an      *)
(* Issuer and a Holder. It is implemented over the Two-Phase Commit         *)
(* protocol, in which a Voucher Transaction Provider  (VTP) coordinates the  *)
(* Voucher Issuers  (Is) to cancel vouchers  (Vs) to Voucher Holders  (Hs) as  *)
(* described in the VoucherLifeCycle specification module. In this          *)
(* specification, Hs and Is spontaneously issue Prepared messages. We       *)
(* ignore the Prepare messages that the VTP can send to the Hs and Is.      *)
(***************************************************************************)

CONSTANTS 
  V = {v1, v2, v3} (* The set of Vouchers *)
  H = {holder1, holder2, holder3} (* The set of Voucher Holders *)
  I = {issuer1, issuer2, issuer3} (* The set of Voucher Issuers *)
  
(* The state of voucher v. *)
\*TypeOK for vState[v]
DEFINE
  vState[v] == [TRUE -> holder, FALSE -> issuer][v IN V]

(* The state of the voucher life cycle machine. *)
\*TypeOK for vlcState[v]
DEFINE
  vlcState[v] == [holder -> 'Active', issuer -> 'Canceled'][vState[v]]

(* The state of voucher holder h. *)
\*TypeOK for hState[h]
DEFINE
  hState[h] == [TRUE -> prepared, FALSE -> unprepared][h IN H]

(* The state of voucher issuer i. *)
\*TypeOK for iState[i]
DEFINE
  iState[i] == [TRUE -> prepared, FALSE -<｜begin▁of▁sentence｜> unprepared][i IN I]

(* The set of all possible messages. *)
msgs == {Prepared} \/ (h >< v) \/ (i >< v) (* Messages of type "Prepared" are sent from the H indicated by the message's vh field to the VTP, and similarly for I *)

(* The state predicate asserting that a H and an I have not reached conflicting decisions. It is an invariant of the specification. *)
\*TypeOK for VTPConsistent
DEFINE 
  VTPConsistent == \A h:H, i:I : (hState[h] = prepared -> vlcState[v] = 'Active' -> iState[i] != prepared) /\ (iState[i] = prepared -> vlcState[v] = 'Active' -> hState[h] != prepared)

(* The complete spec of the a Voucher Cancel using Two-Phase Commit protocol. *)
\*TypeOK for VTPSpec
DEFINE 
  VTPSpec == 
    (* The VTP receives a "Prepared" message from Voucher Holder h and the Voucher Issuer i. We could add the additional enabling condition h,i \notin vtpCPrepared *)
    [(hState[h] = prepared /\ iState[i] = prepared) -> (vlcState[v] = 'Active')] 
    ===> (* The VTP Cancels the voucher; enabled iff the VTP is in its initial state and every H and I has sent a "Prepared" message. *)
    [(hState[h] != prepared /\ iState[i] != prepared) -> (vlcState[v] = 'Canceled')] 
    ===> (* The VTP spontaneously aborts the transaction. *)
    [TRUE -> vlcState[v] = 'Aborted']

(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. Invariance of this conjunction is equivalent to invariance of both of the formulas VTPTypeOK and VTPConsistent. *)
THM_INVARIANT 
  [VTPTypeOK, VTPConsistent] ==> VTPSpec

(* This theorem asserts that the specification VTPSpec of the Two-Phase Commit protocol implements the specification VSpec of the Voucher life cycle specification. *)
THM_IMPLEMENTS 
  ModuleName /\ VTPSpec ==> VSpec
====