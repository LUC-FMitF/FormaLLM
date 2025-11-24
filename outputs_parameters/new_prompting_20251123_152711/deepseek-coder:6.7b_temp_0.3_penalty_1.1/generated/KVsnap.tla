---- MODULE KVsnap ----
EXTENDS FiniteSets, Naturals, Sequences, ZSequences

CONSTANTS Key = {0, 1} // Example of two keys
       /\ TxId = {0, 1} // Example of two transaction IDs
       /\ NoVal = "NoValue"

VARIABLES store == [k \in Key |-> NoVal],
          tx == {},
          missed == [t \in TxId |-> {}];

ASSUME 
   \* Snapshot isolation invariant
      (tx = {}) -> (\forall k \in Key . (snapshotStore[k] = store[k])) /\
                   (\forall t \in tx . missed[t] = {});

PROCEDURE Read == [k \in Key |-> IF k \in read_keys THEN snapshotStore[k] ELSE NoVal];

PROCEDURE Write == [k \in Key |-> IF k \in write_keys THEN self ELSE snapshotStore[k]];

\* Pluscal algorithm for a simple key-value store with snapshot isolation
algorithm KVsnap is
fair process (t in TxId) 
variables
snapshotStore == [k \in Key |-> NoVal],
read_keys  == {},    
write_keys == {},    
ops == <<>>;   
BEGIN
START: tx := tx union {self};
       snapshotStore := store;
with (rk in SUBSET Key \{ {} }; wk in SUBSET Key \{ {} }) 
read_keys  := rk;     
write_keys := wk;    
READ: ops := ops \o SetToSeq({rOp(k, snapshotStore[k]): k in read_keys});
UPDATE: snapshotStore := [k \in Key |-> IF k in write_keys THEN self ELSE snapshotStore[k] ];
COMMIT: if (missed[self] intersect write_keys = {}) 
        then begin
               take self off of active txn set
               tx := tx \{self};
               Update the missed writes for other open transactions (nonlocal update!)
               missed := [o \in TxId |-> IF o in tx THEN missed[o] union write_keys ELSE missed[o]];
               update store
               store := [k \in Key |-> IF k in write_keys THEN snapshotStore[k] ELSE store[k] ];
               log reads for CC isolation check
               ops := ops \o SetToSeq({wOp(k, self): k in write_keys});
             end
END KVsnap.
====