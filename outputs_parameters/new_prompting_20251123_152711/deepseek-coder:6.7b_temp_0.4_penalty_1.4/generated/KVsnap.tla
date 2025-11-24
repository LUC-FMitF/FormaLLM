---- MODULE KVsnap ----
(***************************************************************************)
(* The set of all keys                                                       *)
VARIABLES Key = {0,1} \ UNION {2,3} \ UNION ... \ UNION {N};

(* The set of all transaction IDs                                             *)
VARIABLES TxId = {0,1} \ UNION {2,3} \ UNION ... \ UNION {M};

(* NoVal, which all keys are initialized with                                *)
CONSTANT NoVal = 0;

(* Instantiating ClientCentric enables us to check transaction isolation       *)
(* guarantees this model satisfies                                          *)
INSTANCE ClientCentric;

(* A data store mapping keys to values                                         *)
VARIABLES store = [k \in Key |-> NoVal];

(* The set of open snapshot transactions                                      *)
VARIABLES tx = {};

(* The set of writes invisible to each transaction                             *)
VARIABLES missed = [t \in TxId |-> {}];

(* Transaction processing                                                      *)
PROCEDURE fair process (t \in TxId)
  VARIABLES snapshotStore = [k \in Key |-> NoVal],
            read_keys  = {},
            write_keys = {},
            ops = <<>>;
BEGIN
  START: (* Start the transaction                                               *)
    tx := tx \union {self};
    snapshotStore := store;
    with (rk \in SUBSET Key \ { {} }; wk \in SUBSET Key \ { {} }) do
      read_keys  := rk,
      write_keys := wk;
    END;
    
    READ: (* Process reads on my snapshot                                      *)
      ops := ops \o SetToSeq({rOp(k, snapshotStore[k]): k \in read_keys});
      
    UPDATE: (* Process writes on my snapshot, write 'self' as value             *)
      snapshotStore := [k \in Key |-> IF k \in write_keys THEN self ELSE snapshotStore[k]];
      
    COMMIT: (* Commit the transaction to the database if there is no conflict   *)
      IF (missed[self] \intersect write_keys = {}) THEN
        take self off of active txn set
        tx := tx \ {self};
        Update the missed writes for other open transactions (nonlocal update!)
        missed := [o \in TxId |-> IF o \in tx THEN missed[o] \union write_keys ELSE missed[o]];
        update store
        store := [k \in Key |-> IF k \in write_keys THEN snapshotStore[k] ELSE store[k]];
        log reads for CC isolation check
        ops := ops \o SetToSeq({wOp(k, self): k \in write_keys});
      END;
END;
END.
====