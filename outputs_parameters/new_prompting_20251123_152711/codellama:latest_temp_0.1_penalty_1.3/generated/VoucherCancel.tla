---- MODULE VoucherCancel ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 0..(n-1)  *)
(* (the set {0, 1, ... , n-1}).                                            *)
(***************************************************************************)
CONSTANTS V = <<voucher1, voucher2, voucher3>> : Set((V))
H = <<holder1, holder2, holder3>>:Set ((H) )
I=<<issuer1, issuer2, issuer3> >>: SET ( I ) 
INVARIANTS VTPTypeOK(vtp), VTPConsistent(h, i): BOOLEAN
====