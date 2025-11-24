---- MODULE VoucherTransfer ----
(***************************************************************************)
(* Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.         *)
(* Released under the terms of the Apache License 2.0                        *)
(* See: file LICENSE that came with this software for details.               *)
(* This file contains Intellectual Property that belongs to                  *)
(* Backyard Innovations Pte Ltd., Singapore.                                 *)
(* Authors: Santhosh Raju  <santhosh@byisystems.com>                        *)
(* Cherry G. Mathew <cherry@byisystems.com>                                  *)
(* Fransisca Andriani <sisca@byisystems.com>                                  *)
(***************************************************************************)

EXTENDS VoucherLifeCycle

\* The set of all possible messages
MESSAGES == UNION {Prepared}

TYPEOK INVARIANT 
== (VTPTypeOK /\ VTPConsistent)

(*The initial predicate*)
INITIAL_CONDITIONS 
== (VTP = {} /\ vState[v] in VoucherLifeCycle.Initial_State /\ shState[sh], dhState[dh] \in Initial_State ) FORALL v, sh, dh INSTANCES OF Vouchers, SHs, DHs

(*VTP receives a "Prepared" message from Source Voucher Holder sh and the Destination Voucher Holder dh*)
ON PREPARED[v, sh, dh] FROM (shState[sh], dhState[dh]) 
== EXIST s \in SHs U DHs : (sh, dh) = s /\ vState[v](s) = Prepared FORALL v, sh, dh INSTANCES OF Vouchers, SHs, DHs

(*VTP Transfers the voucher*)
ON TRANSFER FROM (VTP, msgs) 
== EXIST s \in SHs U DHs : (shState[s], dhState[s]) = Transferred FORALL sh, dh INSTANCES OF SHs, DHs
(*VTP spontaneously aborts the transaction*)
ON ABORT FROM VTP == TRUE

(*Source Voucher holder sh prepares*)
ON PREPARE[v, sh] FROM (shState[sh]) 
== EXIST s \in SHs : (shState[s]) = Prepared FORALL v, sh INSTANCES OF Vouchers, SHs
(*Source Voucher holder sh is told by the VTP to Transfer*)
ON TRANSFER FROM (VTP U {Prepared(v, sh, dh)}) 
== EXIST s \in SHs : (shState[s]) = Transferring FORALL v, sh, dh INSTANCES OF Vouchers, SHs, DHs
(*Source Voucher holder sh is told by the VTP to abort*)
ON ABORT FROM (VTP U {Prepared(v, sh, dh)}) 
== EXIST s \in SHs : (shState[s]) = Aborted FORALL v, sh, dh INSTANCES OF Vouchers, SHs, DHs
(*Destination Voucher holder dh prepares*)
ON PREPARE[v, dh] FROM (dhState[dh]) 
== EXIST s \in DHs : (dhState[s]) = Prepared FORALL v, dh INSTANCES OF Vouchers, DHs
(*Destination Voucher holder dh is told by the VTP to Transfer*)
ON TRANSFER FROM (VTP U {Prepared(v, sh, dh)}) 
== EXIST s \in DHs : (dhState[s]) = Transferring FORALL v, sh, dh INSTANCES OF Vouchers, SHs, DHs
(*Destination Voucher holder dh is told by the VTP to abort*)
ON ABORT FROM (VTP U {Prepared(v, sh, dh)}) 
== EXIST s \in DHs : (dhState[s]) = Aborted FORALL v, sh, dh INSTANCES OF Vouchers, SHs, DHs

(*A state predicate asserting that a SH and an DH have not reached conflicting decisions*)
CONSISTENT INVARIANT 
== NOT EXIST s \in SHs U DHs : (shState[s], dhState[s]) = Aborted FORALL sh, dh INSTANCES OF SHs, DHs

(*The complete spec of the a Voucher Transfer using Two-Phase Commit protocol*)
SPECIFICATION 
== (TYPEOK /\ CONSISTENT)
====