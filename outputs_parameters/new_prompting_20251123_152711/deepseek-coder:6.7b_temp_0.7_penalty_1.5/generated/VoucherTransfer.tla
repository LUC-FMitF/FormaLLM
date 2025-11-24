---- MODULE VoucherTransfer ----
(***************************************************************************)
(* Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.          *)
(* Released under the terms of the Apache License 2.0                          *)
(* See: file LICENSE that came with this software for details.                *)
(* This file contains Intellectual Property that belongs to                    *)
(* Backyard Innovations Pte Ltd., Singapore.                                  *)
(* Authors: Santhosh Raju <santhosh@byisystems.com>                          *)
(* Cherry G. Mathew <cherry@byisystems.com>                                   *)
(* Fransisca Andriani <sisca@byisystems.com>                                  *)
(***************************************************************************)

EXTENDS VoucherLifeCycle

\* The set of all possible messages.  Messages of type "Prepared" are sent from the SH indicated by the message's vsh field to the VTP. Similar "Prepared" is also sent from DH indicated by message's vdh field to the VTP. Messages of type "Transfer" and "Abort" are broadcast by the VTP, to be received by all SHs and DHs. The set msgs contains just a single copy of such a message. Receipt of the same message twice is therefore allowed; but in this particular protocol, that's not a problem.                                                       *)
\* -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*)

CONSTANTS 
  V  = {v1, v2, v3}                     \* The set of Vouchers *\)
  SH = {src1, src2, src3}               \* The set of "Source" Voucher Holders *\)
  DH = {dst1, dst2, dst3}               \* The set of "Destination" Voucher Holders *\)
  
VARIABLES
  msgs    == {}                          \* Variable to store all messages sent. Initially no message has been sent. *\)
  vState[v] == UNKNOWN                    \* State of each voucher *\)
  vlcState[v] == UNKNOWN                  \* State of the life cycle of each voucher *\)
  machine  == MACHINE VTPSpec /\ Init /\ Accepts msgs            \* Machine for the VTP *\)
  shState[sh] == UNKNOWN                 \* State of each Source Voucher Holder *\)
  dhState[dh] == UNKNOWN                 \* State of each Destination Voucher Holder *\)
  
\* The state predicate asserting that a SH and an DH have not reached conflicting decisions. It is an invariant of the specification. *\)
VTPTypeOK == 
  [G ~(sh /= dh)] 

\* A state predicate asserting VTPConsistent asserts that for every voucher v, if shState[vsh] = prepared and dhState[dh] = prepared then vlcState[v] = active *\)
VTPConsistent == 
  [G (IFEXISTS vsh,dh ((shState[vsh] = prepared /\ dhState[dh] = prepared) ==> vlcState[v] = active)] )
  
INVARIANT VTPTypeOK /\ VTPConsistent
SPECIFICATION VTPSpec 

(* ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*)
\* This theorem asserts the truth of the temporal formula whose meaning is that the state predicate VTPTypeOK /\ VTPConsistent is an invariant of the specification VTPSpec. Invariance of this conjunction is equivalent to invariance of both of the formulas VTPTypeOK and VTPConsistent.                                                      *)
(* ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------*)
====