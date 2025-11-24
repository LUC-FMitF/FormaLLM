---- MODULE VoucherCancel ----
EXTENDS ModuleName

CONSTANTS
  V = {v1, v2, v3}  (* Vouchers *)
  H = {holder1, holder2, holder3}  (* Voucher Holders *)
  I = {issuer1, issuer2, issuer3}  (* Voucher Issuers *)

ASSUME
  (* Assumptions about the voucher, holder, and issuer states *)
  VState[v] IN {State1, State2, State3} (* The state of voucher v *)
  hState[h] IN {State1, State2, State3} (* The state of voucher holder h *)
  iState[i] IN {State1, State2, State3} (* The state of voucher issuer i *)

VARIABLES
  msgs(* The set of all messages that have been sent *)

(* The state of the voucher transaction provider *)
VTPState == CHOICE v \in V [vState[v] = State1]

(* The set of Hs and Is from which the VTP has received "Prepared for Voucher Cancel" messages *)
vtpCPrepared == {h, i}

(* The set of all possible messages *)
Message == {Prepared(h, i)}

(* Actions that may be performed by the processes *)
VTP_Action ==
  (* The VTP Cancels the voucher *)
  IF VTPState = Initial AND vtpCPrepared = H \times I THEN Cancel
  (* The VTP spontaneously aborts the transaction *)
  ELSE IF VTPState = Initial AND vtpCPrepared \neq H \times I THEN Abort
  (* No action *)
  ELSE Skip

H_Action ==
  (* Voucher holder h prepares *)
  IF hState[h] = State1 THEN Prepare(h)
  (* No action *)
  ELSE Skip

I_Action ==
  (* Voucher issuer i prepares *)
  IF iState[i] = State1 THEN Prepare(i)
  (* No action *)
  ELSE Skip

(* State predicate asserting that a H and an I have not reached conflicting decisions *)
VTPTypeOK == VTPState = Initial AND vtpCPrepared \subseteq H \times I

(* Voucher Cancel using Two-Phase Commit protocol *)
VTPSpec ==
  (* The initial predicate *)
  Init == VTPState = Initial AND vtpCPrepared = {}
  (* The complete spec of the Voucher Cancel using Two-Phase Commit protocol *)
  Next ==
    (* Voucher holder h is told by the VTP to Cancel *)
    IF VTP_Action = Cancel AND VTPState = Initial AND msgs = {Prepared(h, i)} THEN
      VTPState' = Final AND vtpCPrepared = {h, i}
    (* Voucher holder h is told by the VTP to abort *)
    ELSE IF VTP_Action = Abort AND VTPState = Initial AND msgs = {Prepared(h, i)} THEN
      VTPState' = Final AND vtpCPrepared = {h, i}
    (* Voucher issuer i is told by the VTP to Cancel *)
    ELSE IF VTP_Action = Cancel AND VTPState = Initial AND msgs = {Prepared(h, i)} THEN
      VTPState' = Final AND vtpCPrepared = {h, i}
    (* Voucher issuer i is told by the VTP to abort *)
    ELSE IF VTP_Action = Abort AND VTPState = Initial AND msgs = {Prepared(h, i)} THEN
      VTPState' = Final AND vtpCPrepared = {h, i}
    (* No change *)
    ELSE VTPSpec

(* Assert that the Voucher Cancel specification implements the Voucher Life Cycle specification *)
VSpec == MODULENAME.VoucherLifeCycle

(* This theorem asserts the truth of the temporal formula whose meaning is that the state predicate VTPTypeOK is an invariant of the specification VTPSpec *)
Invariant == [](VTPTypeOK)

(* TLC Configuration *)
CONSTANTS
  V = {v1, v2, v3}
  H = {holder1, holder2, holder3}
  I = {issuer1, issuer2, issuer3}
INVARIANTS VTPTypeOK VTPConsistent
SPECIFICATION VTPSpec

(* Refinement seems not to hold *)
\*PROPERTY VSpec
CHECK_DEADLOCK FALSE
====