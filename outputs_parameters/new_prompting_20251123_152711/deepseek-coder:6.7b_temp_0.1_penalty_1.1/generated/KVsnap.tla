---- MODULE KVsnap ----
(***************************************************************************)
(* Defines a simple key-value store with snapshot isolation.               *)
(* This version has atomic updates of store and missed sets of txns.        *)
(***************************************************************************)

EXTENDS ClientCentric

CONSTANTS
Key == {0, 1}
TxId == {0, 1}
NoVal == NULL

VARIABLES
store == [k \in Key |-> NoVal],
tx == {},
missed == [t \in TxId |-> {}];

Invariants
SnapshotIsolation == \A t \in TxId : missed[t] \cap write_keys = {}
TypeOK == \A k \in Key : store[k] = NoVal \/ store[k] \in tx

FairProcess == \A t \in TxId : tx \cap read_keys \cap write_keys = {}

\* Algorithm for a simple key-value store with snapshot isolation
algorithm KVsnap {
variables
snapshotStore == [k \in Key |-> NoVal],
read_keys == {},
write_keys == {},
ops == <<>>;

BEGIN:
tx := tx \union {self};
snapshotStore := store;
with (rk \in SUBSET Key \ { {} }; wk \in SUBSET Key \ { {} }) {
read_keys := rk;
write_keys := wk;
};
READ:
ops := ops \o SetToSeq({rOp(k, snapshotStore[k]): k \in read_keys});
UPDATE:
snapshotStore := [k \in Key |-> IF k \in write_keys THEN self ELSE snapshotStore[k]];
COMMIT:
IF (missed[self] \intersect write_keys = {}) {
tx := tx \ {self};
missed := [o \in TxId |-> IF o = self THEN missed[o] \union write_keys ELSE missed[o]];
store := [k \in Key |-> IF k \in write_keys THEN snapshotStore[k] ELSE store[k]];
ops := ops \o SetToSeq({wOp(k, self): k \in write_keys});
}
}

\* Allow infinite stuttering to prevent deadlock on termination
StutterFree == \A s \in State : s \in State

=============================================================================
====
BEGIN TRANSLATION (chksum(pcal) = "1adfcb46" /\ chksum(tla) = "5b28617f")
END TRANSLATION
====