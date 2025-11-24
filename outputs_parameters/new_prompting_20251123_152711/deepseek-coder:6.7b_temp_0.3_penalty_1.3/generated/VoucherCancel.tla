---- MODULE VoucherCancel ----
EXTENDS ModuleNameForExtendedModule -- replace with actual module name if needed

(***************************************************************************)
(* This specification describes the cancellation of Voucher between an      *)
(* Issuer and a Holder. It is implemented over the Two-Phase Commit         *)
(* protocol, in which a Voucher Transaction Provider (VTP) coordinates the  *)
(* Voucher Issuers to cancel vouchers to Voucher Holders as described in   *)
(* the VoucherLifeCycle specification module. In this specification, Hs and Is*)
(* spontaneously issue Prepared messages. We ignore the Prepare messages that *)
(* the VTP can send to the Hs and Is.                                      *)
(***************************************************************************)

VARIABLES 
    msgs : {Prepared}, -- set of all possible messages, including "Prepared"
    vtpCPrepared : (H \times I) -> BOOLEAN -- VTP's copy prepared relation
LOCAL INSTANCE ModuleNameForExtendedModule -- replace with actual module name if needed
  
\* The state of the voucher transaction provider. 
vState[v] == ... (* define your invariant here *)

\* The state of the voucher life cycle machine for a given Voucher v, h and i.
vlcState[(v,h,i)] == 
    CASE (...) OF {...} -- replace with actual definition based on vouchers states 
  
\* The state of each Holder is represented by:
hState[h] == ... (* define your invariant here *)

\* The state of each Issuer i.
iState[i] == 
    CASE (...) OF {...} -- replace with actual definition based on issuers states 
  
(* Define all symbols before use, and type OK for invariants *)
CONSTANTS VTPTypeOK = ... (* define your invariant here *)
CONSTANTS VTPConsistent = ... (* define your invariant here *)
SPECIFICATION VTPSpec == -- complete specification of the Two-Phase Commit protocol 
    (...) /\ VTPTypeOK /\ VTPConsistent  
(* Refinement seems not to hold, CHECK_DEADLOCK FALSE is used for a quick check without refinements *)
====