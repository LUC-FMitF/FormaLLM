---- MODULE VoucherCancel ----
(***************************************************************************)
(* This specification describes the cancellation of Voucher between an      *)
(* Issuer and a Holder. It is implemented over the Two-Phase Commit         *)
(* protocol, in which a Voucher Transaction Provider (VTP) coordinates the  *)
(* Voucher Issuers (Is) to cancel vouchers (Vs) to Voucher Holders (Hs) as  *)
(* described in the VoucherLifeCycle specification module. In this          *)
(* specification, Hs and Is spontaneously issue Prepared messages. We       *)
(* ignore the Prepare messages that the VTP can send to the Hs and Is.      *)
(* For simplicity, we also eliminate Abort messages sent by an Hs / Is      *)
(* when it decides to abort.  Such a message would cause the VTP to abort   *)
(* the transaction, an event represented here by the VTP spontaneously      *)
(* deciding to abort.                                                       *)
(***************************************************************************)
(* Receipt of the same message twice is therefore allowed; but in this     *)
(* particular protocol, that's not a problem.                           *)
(***************************************************************************)
(* The set of all possible messages.  Messages of type "Prepared" are     *)
(* sent from the H indicated by the message's vh field to the VTP.        *)
(* Similar "Prepared" is also sent from I indicated by message's vc       *)
(* field to the VTP. Messages of type "Cancel" and  "Abort" are broadcast  *)
(* by the VTPs, to be received by all Hs and Is. The set msgs contains   *)
(* just a single copy of such a message.                                  *)
(***************************************************************************)
(* This theorem asserts the truth of the temporal formula whose meaning   *)
(* is that the state predicate VTPTypeOK  /\ VTPConsistent is an           *)
(* invariant of the specification VTPSpec. Invariance of this             *)
(* conjunction is equivalent to invariance of both of the formulas        *)
(* VTPTypeOK and VTPConsistent.                                           *)
(***************************************************************************)
(* This theorem asserts that the specification VTPSpec of the Two-Phase   *)
(* Commit protocol implements the specification VSpec of the              *)
(* Voucher life cycle specification.                                      *)
(***************************************************************************)

\* The set of all possible messages
Msgs == {"Prepared", "Cancel", "Abort"}

\* Type-correctness invariant
VTPTypeOK  /\  VTPConsistent  /\  ...

\* Initial predicate
Init == 

\* Actions performed by the processes (not included)
Actions == {Action1, Action2, ...}

\* Specification of the voucher cancel using Two-Phase Commit protocol
VTPSpec == ...

\* Voucher life cycle specification
VSpec == 

=============================================================================
====