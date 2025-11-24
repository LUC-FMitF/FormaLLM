---- MODULE VoucherCancel ----
EXTENDS VoucherLifeCycle
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
  
(* State predicates *)
vState[v] == v \in V
hState[h] == h \in H
iState[i] == i \in I

(* The state of the voucher transaction provider. *)
VTPState == [v \in V |-> (vState[v])]

(* The set of Hs and Is from which the VTP has received "Prepared for Voucher Cancel" messages. *)
vtpCPrepared == DOMAIN VTPState

(* Type-correctness invariant *)
VTPTypeOK == 
  \E v \in V, h \in H, i \in I : (hState[h] /\ iState[i]) => ((h = vtpState[v].h) /\ (i = vtpState[v].i))
  
(* Consistency invariant *)
VTPConsistent == 
  \E h \in H, i \in I : (hState[h] /\ iState[i]) => ((h = vtpState[v].h) /\ (i = vtpState[v].i)) forall v in V
  
(* The initial predicate. *)
Init == VTPTypeOK /\ VTPConsistent

(* Actions that may be performed by the processes, first the VTP's actions, the Hs' actions, then the Is' actions. *)
Next[vtpState] == 
  { [v \in V |-> (vState[v])] : vtpState in Init /\ (\E h \in H, i \in I : (hState[h] /\ iState[i])) }
  
(* The complete spec of the a Voucher Cancel using Two-Phase Commit protocol. *)
VTPSpec == {Init} UNION {Next[vtpState] : vtpState in Init*}

(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
VoucherCancelTheorem == 
  \A vtpState \in Init* : (vtpState -> VTPTypeOK) /\ (vtpState -> VTPConsistent)
  
(* This theorem asserts that the specification VTPSpec of the Two-Phase Commit protocol implements the specification VSpec of the Voucher life cycle specification. *)
RefinementTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the specification VTPSpec of the Two-Phase Commit protocol implements the specification VSpec of the Voucher life cycle specification. *)
RefinementTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle.VSpec)
  
(* This theorem asserts that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. *)
InvariantTheorem == 
  \A vtpState \in Init* : (vtpState -> VoucherLifeCycle<｜begin▁of▁sentence｜>
====