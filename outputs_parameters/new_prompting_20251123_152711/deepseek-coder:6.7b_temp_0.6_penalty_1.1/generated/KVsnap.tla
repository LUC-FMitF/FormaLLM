---- MODULE KVsnap ----

(******************************************************************************)
(* A data store mapping keys to values                                     *)
(* The set of open snapshot transactions                                    *)
(* The set of writes invisible to each transaction                          *)
(* See end of file for invariants                                          *)
(* Transaction processing                                                   *)
(* local snapshot of the store                                             *)
(* read keys  for the transaction                                         *)
(* write keys for the transaction                                         *)
(* a log of reads & writes this transaction executes; used for interfacing to CC*)
(******************************************************************************)

EXTENDS ClientCentric

CONSTANTS Key = {...} (* The set of all keys *)
CONSTANTS TxId = {...} (* The set of all transaction IDs *)
CONSTANTS NoVal = ... (* NoVal, which all keys are initialized with *)

VARIABLES
  store == [k \in Key |-> NoVal], (* A data store mapping keys to values *)
  tx == {}, (* The set of open snapshot transactions *)
  missed == [t \in TxId |-> {}], (* The set of writes invisible to each transaction *)
  ops == <<>>, (* a log of reads & writes this transaction executes; used for interfacing to CC *)

INVARIANTS
  (* Snapshot isolation invariant: no transaction can see changes made by other transactions before it starts. *)
  InvSnapshotIsolation == \A t \in tx : (\A k \in Key : snapshotStore[k] = store[k]) /\ (missed[t] = {})

DEFINE
  (* Process reads on my snapshot *)
  rOp(k, v) == <<k->v>>,
  (* Process writes on my snapshot, write 'self' as value *)
  wOp(k, v) == <<k->v>>,

(* Algorithm for a simple key-value store with snapshot isolation. *)
PROCEDURE KVsnap IS
  VARIABLES
    snapshotStore == [k \in Key |-> NoVal], (* local snapshot of the store *)
    read_keys  == {}, (* read keys  for the transaction *)
    write_keys == {} (* write keys for the transaction *)
  BEGIN
    START: (* Start the transaction *)
      tx := tx \union {self};
      snapshotStore := store;
      with (rk \in SUBSET Key \ {{} }; wk \in SUBSET Key \ {{} }) DO
        read_keys  := rk, (* select a random read-key-set from possible read-keys *)
        write_keys := wk; (* select a random write-key-set from possible write-keys *)
      END;
    READ: (* Process reads on my snapshot *)
      ops := ops \o SetToSeq({rOp(k, snapshotStore[k]): k \in read_keys});
    UPDATE: (* Process writes on my snapshot, write 'self' as value *)
      snapshotStore := [k \in Key |-> IF k \in write_keys THEN self ELSE snapshotStore[k]];
    COMMIT: (* Commit the transaction to the database if there is no conflict *)
      IF missed[self] \intersect write_keys = {} THEN
        tx := tx \ {self};
        Update the missed writes for other open transactions (nonlocal update!)
        missed := [o \in TxId |-> IF o \in tx THEN missed[o] \union write_keys ELSE missed[o]];
      END;
    (* update store *)
    store := [k \in Key |-> IF k \in write_keys THEN snapshotStore[k] ELSE store[k]];
  END KVsnap
END
====