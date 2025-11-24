---- MODULE KVsnap ----
MODULE KVsnap
VARIABLES
    A DataStore : Key -> Value
    store : DataStore = {}
    openTransactions : Set<TxId> = {}
    writeInvisibleTo : Set<TxId> = {}
END KVsnap

INVARIANT NoValueInitialized(k : Key) :=
    ALL (k )\in Key => ALL (A[k]) = NoVal

INSTANTANCE NoValueInitialized(k : Key)
VARIABLES k

INVARIANT TransactionIsolation :=
    ALL txId ∈ openTransactions ∧ ALL txId ∈ writeInvisibleTo ⊛ A ≠ NoVal

INSTANCE TransactionIsolation
VARIABLES txId

LOCAL TransactionProcessing(t : TxId) :=
    IF t ∈ openTransactions THEN
        let
            snapshotStore : DataStore = {}
            read_keys : Set<Key> = {}
            write_keys : Set<Key> = {}
            ops : Ops = {}
        IN
            REPEAT
                snapshotStore := [k → NoVal] / [k ∈ read_keys → A[k]] / [k ∈ write_keys → snapshotStore[k]]
                read_keys := {k ∈ SUBSET Key {}}
                write_keys := {k ∈ SUBSET Key {}}
            OD
            ops := ops ∪ SetToSeq({rOp(k, snapshotStore[k]): k ∈ read_keys})
            ops := ops ∪ SetToSeq({wOp(k, self): k ∈ write_keys})
            IF NOT (missed[t] ∩ write_keys = {}) THEN
                update store := [k ∈ write_keys → self] / [k ∉ write_keys → store[k]]
                missed := [t ∈ openTransactions → missed[t] ∪ write_keys]
            END
        OD

INSTANCE TransactionProcessing(t)
VARIABLES t

INVARIANT SnapshotIsolation :=
    ALL snapshotStore : DataStore => ALL snapshotStore ≠ NoVal

INSTANCE SnapshotIsolation
VARIABLES snapshotStore

INVARIANT Serializability :=
    ALL t : TxId => NOT (missed[t] ∩ write_keys = {})

INSTANCE Serializability
VARIABLES t

END KVsnap
====