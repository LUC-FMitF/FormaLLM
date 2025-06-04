--------------------------- MODULE KVsnap ---------------------------------

EXTENDS Integers, Sequences, FiniteSets, Util

CONSTANTS   Key,
TxId,
NoVal

CC == INSTANCE ClientCentric WITH Keys <- Key, Values <- TxId \union {NoVal}

wOp(k,v) == CC!w(k,v)
rOp(k,v) == CC!r(k,v)
InitialState == [k \in Key |-> NoVal]
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

VARIABLES store, tx, missed, pc, snapshotStore, read_keys, write_keys, ops

vars == << store, tx, missed, pc, snapshotStore, read_keys, write_keys, ops
>>

ProcSet == (TxId)

Init ==
/\ store = [k \in Key |-> NoVal]
/\ tx = {}
/\ missed = [t \in TxId |-> {}]

/\ snapshotStore = [self \in TxId |-> [k \in Key |-> NoVal]]
/\ read_keys = [self \in TxId |-> {}]
/\ write_keys = [self \in TxId |-> {}]
/\ ops = [self \in TxId |-> <<>>]
/\ pc = [self \in ProcSet |-> "START"]

START(self) == /\ pc[self] = "START"
/\ tx' = (tx \union {self})
/\ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
/\ \E rk \in SUBSET Key \ { {} }:
\E wk \in SUBSET Key \ { {} }:
/\ read_keys' = [read_keys EXCEPT ![self] = rk]
/\ write_keys' = [write_keys EXCEPT ![self] = wk]
/\ pc' = [pc EXCEPT ![self] = "READ"]
/\ UNCHANGED << store, missed, ops >>

READ(self) == /\ pc[self] = "READ"
/\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({rOp(k, snapshotStore[self][k]): k \in read_keys[self]})]
/\ pc' = [pc EXCEPT ![self] = "UPDATE"]
/\ UNCHANGED << store, tx, missed, snapshotStore, read_keys,
write_keys >>

UPDATE(self) == /\ pc[self] = "UPDATE"
/\ snapshotStore' = [snapshotStore EXCEPT ![self] = [k \in Key |-> IF k \in write_keys[self] THEN self ELSE snapshotStore[self][k] ]]
/\ pc' = [pc EXCEPT ![self] = "COMMIT"]
/\ UNCHANGED << store, tx, missed, read_keys, write_keys, ops >>

COMMIT(self) == /\ pc[self] = "COMMIT"
/\ IF missed[self] \intersect write_keys[self] = {}
THEN /\ tx' = tx \ {self}
/\ missed' = [o \in TxId |-> IF o \in tx' THEN missed[o] \union write_keys[self] ELSE missed[o]]
/\ store' = [k \in Key |-> IF k \in write_keys[self] THEN snapshotStore[self][k] ELSE store[k] ]
/\ ops' = [ops EXCEPT ![self] = ops[self] \o SetToSeq({wOp(k, self): k \in write_keys[self]})]
ELSE /\ TRUE
/\ UNCHANGED << store, tx, missed, ops >>
/\ pc' = [pc EXCEPT ![self] = "Done"]
/\ UNCHANGED << snapshotStore, read_keys, write_keys >>

t(self) == START(self) \/ READ(self) \/ UPDATE(self) \/ COMMIT(self)

Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
/\ UNCHANGED vars

Next == (\E self \in TxId: t(self))
\/ Terminating

Spec == /\ Init /\ [][Next]_vars
/\ \A self \in TxId : WF_vars(t(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

SnapshotIsolation == CC!SnapshotIsolation(InitialState, Range(ops))

TypeOK ==
/\ store \in [Key -> TxId \union {NoVal}]
/\ tx \subseteq TxId
/\ missed \in [TxId -> SUBSET Key]

Serialization == CC!Serializability(InitialState, Range(ops))

===========================================================================
As an exercise try to add more yield points, make the actions smaller.
Especially see if you can pull out something from the atomic "COMMIT" label to earlier, and see what breaks.
