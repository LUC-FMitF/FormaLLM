---- MODULE KVsnap ----
EXTENDS FiniteSets, Naturals, Sequences, ZSequences

CONSTANTS
  Key == {0, 1, ..., 1000}
  TxId == {0, 1, ..., 1000}
  NoVal == NULL

VARIABLES
  store == [k \in Key |-> NoVal],
  tx == {},
  missed == [t \in TxId |-> {}],
  ops == <<>>;

PROCEDURE Read == \k ==> snapshotStore[k];
PROCEDURE Write == \k ==> self;

INVARIANT SnapshotIsolation == \seq ==>
  LET
    readTx == {t \in tx |-> seq INTERSECT ops[t]},
    writeTx == {t \in tx |-> seq INTERSECT ops[t]},
    readKeys == UNION {rk \in readTx |-> ops[rk].read},
    writeKeys == UNION {wk \in writeTx |-> ops[wk].write}
  IN
    readKeys \subseteq writeKeys \/ writeKeys = {};

INVARIANT Serializability == \seq ==>
  LET
    readTx == {t \in tx |-> seq INTERSECT ops[t]},
    writeTx == {t \in tx |-> seq INTERSECT ops[t]},
    readKeys == UNION {rk \in readTx |-> ops[rk].read},
    writeKeys == UNION {wk \in writeTx |-> ops[wk].write}
  IN
    readKeys \cap writeKeys = {};

PROCEDURE fairProcess(t \in TxId)
  VARIABLES
    snapshotStore == [k \in Key |-> NoVal],
    read_keys == {},
    write_keys == {},
    ops == <<>>;
  BEGIN[2](
    START:
      tx := tx \union {self};
      snapshotStore := store;
      WITH (rk \in SUBSET Key \ { {} }; wk \in SUBSET Key \ { {} }) {
        read_keys := rk;
        write_keys := wk;
      };
    READ:
      ops := ops \o SetToSeq({rOp(k, snapshotStore[k]): k \in read_keys});
    UPDATE:
      snapshotStore := [k \in Key |-> IF k \in write_keys THEN self ELSE snapshotStore[k]];
    COMMIT:
      IF (missed[self] \intersect write_keys = {}) THEN
        tx := tx \ {self};
        missed := [o \in TxId |-> IF o \in tx THEN missed[o] \union write_keys ELSE missed[o]];
        store := [k \in Key |-> IF k \in write_keys THEN snapshotStore[k] ELSE store[k]];
        ops := ops \o SetToSeq({wOp(k, self): k \in write_keys});
      END
  END

ALGORITHM KVsnap
  VARIABLES
    data store == [k \in Key |-> NoVal],
    tx == {},
    missed == [t \in TxId |-> {}],
    ops == <<>>;
  BEGIN[2](
    fairProcess(t)
  )
  END
====