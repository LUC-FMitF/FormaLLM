---- MODULE VoucherCancel ----
(***************************************************************************)
(*                                                                         *)
(* Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.        *)
(* Released under the terms of the Apache License 2.0                      *)
(* See: file LICENSE that came with this software for details             *)
(* This file contains Intellectual Property that belongs to                *)
(* Backyard Innovations Pte Ltd., Singapore. Authors: Santhosh Raju <santhosh@byisystems.com>                     Cherry G. Mathew <cherry@byisystems.com>                    Fransisca Andriani <sisca@byisystems.com>                 *)
(* The set of Vouchers                                                        *)
***************************************************************************)
CONSTANTS
  V = {v1, v2, v3}
  H = {holder1, holder2, holder3}
  I = {issuer1, issuer2, issuer3}
INVARIANTS VTPTypeOK VTPConsistent
SPECIFICATION VTPSpec
\* Refinement seems not to hold
\*PROPERTY VSpec
CHECK_DEADLOCK FALSE
====