---- MODULE KVsnap ----
(***************************************************************************)
(* Defines a simple key-value store with snapshot isolation.                *)
(* This version has atomic updates of store and missed sets of txns.          *)
(* See end of file for invariants                                              *)
(***************************************************************************)

CONSTANTS
Key == { ... }  (* The set of all keys *)
TxId == { ... }  (* The set of all transaction IDs *)
NoVal == { ... }  (* NoVal, which all keys are initialized with *)

VARIABLES
store == [k \in Key |-> NoVal],   (* A data store mapping keys to values *)
tx == {},                          (* The set of open snapshot transactions *)
missed == [t \in TxId |-> {}];     (* The set of writes invisible to each transaction *)

(* Transaction processing *)
PROCEDURE fair process (t \in TxId)
VARIABLES
snapshotStore == [k \in Key |-> NoVal],  (* local snapshot of the store *)
read_keys, write_keys == {},            (* read keys and write keys for the transaction *)
ops == <<>>;                            (* a log of reads & writes this transaction executes *)
BEGIN
START: (* Start the transaction *)
tx := tx \union {self};
snapshotStore := store;                  (* take my snapshot of store *)
with (rk \in SUBSET Key \{ {} }; wk \in SUBSET Key \{ {} }) DO
  read_keys := rk,                      (* select a random read-key-set from possible read-keys *)
  write_keys := wk;                     (* select a random write-key-set from possible write-keys *)
END;
READ: (* Process reads on my snapshot *)
ops := ops \o SetToSeq({rOp(k, snapshotStore[k]): k \in read_keys});
UPDATE: (* Process writes on my snapshot, write 'self' as value *)
snapshotStore := [k \in Key |-> IF k \in write_keys THEN self ELSE snapshotStore[k]];
COMMIT: (* Commit the transaction to the database if there is no conflict *)
IF missed[self] \intersect write_keys = {} THEN
  tx := tx \{self};                      (* take self off of active txn set *)
  (* Update the missed writes for other open transactions (nonlocal update!) *)
  missed := [o \in TxId |-> IF o \in tx THEN missed[o] \union write_keys ELSE missed[o]];
  (* update store *)
  store := [k \in Key |-> IF k \in write_keys THEN snapshotStore[k] ELSE store[k]];
  (* log reads for CC isolation check *)
  ops := ops \o SetToSeq({wOp(k, self): k \in write_keys});
END;
END PROCEDURE;

(* Invariants *)
INVARIANT SnapshotIsolation == tx /\ {} = (tx - {self}) \intersect (missed[self] \union write_keys);

BEGIN TRANSLATION  (chksum(pcal) = "1adfcb46" /\ chksum(tla) = "5b28617f")
END TRANSLATION

(* Allow infinite stuttering to prevent deadlock on termination. *)
STUTTER ANY
====