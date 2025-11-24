---- MODULE VoucherTransfer -----------------------------------------------
... (previous module content) ...
=============================================================================
====
(* The set of all possible messages. *)
msgs == {Prepared(vsh, vdh), Transfer, Abort}

\* VTP's actions: Receive a "Prepared" message from Source and Destination Holders 
VTPReceivesPrepareMsgFromSHorDH[next](msg) == 
    CASE msg \in msgs OF {
        Prepared(vsh, vdh): VTPConsistent /\ (vsh, vdh) \notin vtpTPrepared  -> next.VTPReceivesPrepareMsgFromSHorDH[next](msg),
    }

(* The Voucher Transaction Provider's actions: Transfer the voucher *)
VTPCoordinatesTransfer[next] == ((\E sh \in SH : Prepared(sh, dh) \in msgs FORALL dh \in DH)) /\ 
    (\A dh \in DH : VTPReceivesPrepareMsgFromSHorDH[next](Transfer(dh))) -> next.VTPCoordinatesTransfer[next]

(* The Source and Destination Holders' actions: Prepares *)
SHTakesAction == (shState = shWaiting) /\ 
    (\A dh \in DH : dhState = dhWaiting) -> 
        SeqFromZSeq(Rotation([0 |-> vlcState[v]],1)) // {Prepared(sh,dh)}
====