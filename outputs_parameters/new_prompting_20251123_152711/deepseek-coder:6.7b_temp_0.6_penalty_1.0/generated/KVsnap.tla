---- MODULE KVsnap ----
EXTENDS FiniteSets, Naturals

CONSTANTS
Key == {<>}
TxId == {<>}
NoVal == "NoValue"

VARIABLES
store == [k \in Key |-> NoVal],
tx == {},
missed == [t \in TxId |-> {}];

Invariant SnapshotIsolation == \A t \in tx : missed[t] \subseteq read_keys[t]

Invariant Serializability == \A t1, t2 \in tx : IF t1 \neq t2 THEN missed[t1] \cap missed[t2] = {}

Invariant NoWriteSkew == \A t \in tx : \#write_keys[t] = \#missed[t]

PROCEDURE KVsnap ==
VARIABLES
snapshotStore == [k \in Key |-> NoVal],
read_keys == {},
write_keys == {},
ops == <<>>;
[...]
====