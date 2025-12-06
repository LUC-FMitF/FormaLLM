---- MODULE KVsnap ----
(***************************************************************************)
(* Pluscal algorithm for a simple key-value store with snapshot isolation  *)
(* This version has atomic updates of store and missed sets of txns       *)
(***************************************************************************)

VARIABLES
  A data store mapping keys to values
  store = [k \in Key |-> NoVal],
  The set of open snapshot transactions
  tx = {},
  The set of writes invisible to each transaction
  missed = [t \in TxId |-> {}];

TRANSLATION
  BEGIN
    START: \* Start the transaction
    tx := tx \union {self};
    snapshotStore := store; \* take my snapshot of store
    with (rk \in SUBSET Key \ { {} }; wk \in SUBSET Key \ { {} }) {
      read_keys := rk;     \* select a random read-key-set  from possible read-keys
      write_keys := wk;    \* select a random write-key-set from possible write-keys
    };
    READ: \* Process reads on my snapshot
    log reads for CC isolation check
    ops := ops \o SetToSeq({rOp(k, snapshotStore[k]): k \in read_keys});
    UPDATE: \* Process writes on my snapshot, write 'self' as value
    snapshotStore := [k \in Key |-> IF k \in write_keys THEN self ELSE snapshotStore[k] ];
    COMMIT: \* Commit the transaction to the database if there is no conflict
    if (missed[self] \intersect write_keys = {}) {
      take self off of active txn set
      tx := tx \ {self};
      Update the missed writes for other open transactions (nonlocal update!)
      missed := [o \in TxId |-> IF o \in tx THEN missed[o] \union write_keys ELSE missed[o]];
      update store
      store := [k \in Key |-> IF k \in write_keys THEN snapshotStore[k] ELSE store[k] ];
      log reads for CC isolation check
      ops := ops \o SetToSeq({wOp(k, self): k \in write_keys});
    }
  END

GLOBAL VARIABLES
  Process t
  Allow infinite stuttering to prevent deadlock on termination.

INVARIANTS
  Serializability would not be satisfied due to write-skew

*************************************************************************)
====