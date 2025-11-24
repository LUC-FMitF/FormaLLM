---- MODULE VoucherCancel ----
(***************************************************************************)
(* This specification describes the cancellation of Vouchers between a     *)
(* Holder (H) and an Issuer (I). It is implemented over the Two-Phase      *)
(* Commit protocol, in which a transaction provider (VTP) coordinates Hs  *)
(* to cancel vouchers.                                                   *)
(***************************************************************************)

EXTENDS FiniteSets, Naturals, Sequences
  
CONSTANTS
  V = {v1, v2}         (* The set of all possible vouchers                *)
  H = {holder1, holder2}       (* Set of All the Holders                  *)
  I = {issuer1, issuer2}        (* Set Of All Issuers                     *)
  
\* Define a VTP state variable to capture its current state. It can be: Prepared or Aborted. Initialized with an empty set for now.     *\)
VARIABLES vtpState == {}
  hState[h] == 0       (* State of Holder *)
  iState[i] == 1        (* The other issuer's state                     *)
  
\* Define a predicate to check the type-correctness invariant. For now, it returns true for all voucher holders and issuers *\)
PREDICATE VTPTypeOK == TRUE 

(* We have defined invariants as follows:*)
INVARIANT TypeInvariant(v) ==  (Forall h \in H : hState[h] = 0 OR hState[h]=1 ) /\   (* Check the state of Holder *)
                              Forall i \in I :  Issuer_OK   ==> vtpTypeOk     \(* Check VTP type OK*)
                              |-> TRUE
(* Define a predicate to check for consistency. It should be true at all times, but let's define it as false for now *)  
INVARIANT Consistent(v) == FALSE  (* Not implemented yet                  \*\)   
SPECIFICATION VTPSpec ==  [|-> FORALL vh IN H * iState[i] = 1 : h_OK /\ Issuer_Ok ]==>  (Forall v in V: VoucherCancel OK )
====