---- MODULE KVsnap ----
(***************************************************************************)
(* The set of all keys.                                                      *)
(* The set of all transaction IDs.                                            *)
(* NoVal, which all keys are initialized with.                                *)
(* Instantiating ClientCentric enables us to check transaction isolation       *)
(* guarantees this model satisfies                                         *)
(* https://muratbuffalo.blogspot.com/2022/07<｜begin▁of▁sentence｜> 56b9d7e8-f4f5-45ec-a531-c4bf521112d0>
(* for instantiating the ClientCentric module                                  *)
(* A data store mapping keys to values                                         *)
(* The set of open snapshot transactions                                        *)
(* The set of writes invisible to each transaction                             *)
(* See end of file for invariants                                                *)
(* Transaction processing                                                       *)
(* local snapshot of the store                                                   *)
(* read keys  for the transaction                                                *)
(* write keys for the transaction                                                *)
(* a log of reads & writes this transaction executes; used for interfacing to CC   *)
(* Start the transaction                                                        *)
(* take my snapshot of store                                                      *)
(* select a random read-key-set  from possible read-keys                         *)
(* select a random write-key-set from possible write-keys                          *)
(* Process reads on my snapshot                                                   *)
(* log reads for CC isolation check                                             *)
(* Process writes on my snapshot, write 'self' as value                            *)
(* Commit the transaction to the database if there is no conflict                *)
(* take self off of active txn set                                                 *)
(* Update the missed writes for other open transactions  (nonlocal update!)         *)
(* update store                                                                   *)
(* log reads for CC isolation check                                             *)
(***************************************************************************)
(* Pluscal algorithm for a simple key-value store with snapshot isolation       *)
(* This version has atomic updates of store and missed sets of txns                *)
(******************************************************************************)
\*algorithm KVsnap 
variables
store  = [k \in Key |-> NoVal],
tx     = {},
missed = [t \in TxId |-> {}];

fair process (t in TxId)
variables
snapshotStore = [k \in Key |-> NoVal], 
read_keys  = {},     
write_keys = {},     
ops = {};   
{
START: * Start the transaction
tx := tx union {self};
snapshotStore := store; * take my snapshot of store
with (rk in SUBSET Key - {} ; wk in SUBSET Key - {}) 
{
read_keys := rk;      * select a random read-key-set  from possible read-keys
write_keys := wk;     * select a random write-key-set from possible write-keys
};
READ: * Process reads on my snapshot
log reads for CC isolation check
ops := ops union SetToSeq({rOp(k, snapshotStore[k]): k in read_keys});
UPDATE: * Process writes on my snapshot, write 'self' as value
snapshotStore := [k \in Key |-> IF k in write_keys THEN self ELSE snapshotStore[k]];
COMMIT: * Commit the transaction to the database if there is no conflict
if (missed[self] intersect write_keys = {}) 
{
take self off of active txn set
tx := tx - {self};
Update the missed writes for other open transactions (nonlocal update!)
missed := [o \in TxId |-> IF o in tx THEN missed[o] union write_keys ELSE missed[o]];
update store
store := [k \in Key |-> IF k in write_keys THEN snapshotStore[k] ELSE store[k]];
log reads for CC isolation check
ops := ops union SetToSeq({wOp(k, self): k in write_keys});
}
END PROCEDURE KVsnap
=============================================================================
====
CONSTANTS 
NoVal = "no-value" (* All keys are initialized with this value *)
TxId  = {0 .. }    (* Set of all transaction IDs, start from 0 *)
Key   = {...}      (* Set of all keys. Should be defined before use *)
====
SPECIFICATION Spec == ! [KVsnap]FairReach(~"Start", ~"END PROCEDURE KVsnap")
INVARIANTS Inv == ... (* Invariants go here, for example: 
                          StoreInv :== \A k \in Key |-> snapshotStore[k] = store[k], 
                         which states that the local copy of each key in the store is up to date. *)
====