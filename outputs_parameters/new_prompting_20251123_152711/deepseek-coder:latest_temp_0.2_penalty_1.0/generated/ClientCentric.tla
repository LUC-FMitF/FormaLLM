---- MODULE ClientCentric ----
MODULE TLA+

CONSTANTS
  InitValue  _|_
  TimeStamp  _|_
  Values     _|_
  Keys       _|_
  Writes      _|_
  Reads       _|_
  Transactions _|_
  ExecutionElem _|_
  State _|_
  Operation _|_
  Transaction _|_
  ReadState _|_
  Execution _|_
  ExecutionElems _|_
  CT_SER _|_
  CT_SSER _|_
  SnapshotIsolation _|_
  StrictSerializability _|_
  ReadCommitted _|_
  ReadUncommitted _|_
  CheckTypes _|_
  PrintT _|_
  SerializabilityDebug _|_
  Serializability _|_
  TLA+Config _|_

SPECIFICATION TLC Config

INVARIANTS
  InitValue
  TimeStamp
  Values
  Keys
  Writes
  Reads
  Transactions
  ExecutionElem
  State
  Operation
  Transaction
  ReadState
  Execution
  ExecutionElems
  CT_SER
  CT_SSER
  SnapshotIsolation
  StrictSerializability
  ReadCommitted
  ReadUncommitted
  CheckTypes

LOCAL INSTANCE TLA+Config

LOCAL INSTANCE InitValue
LOCAL INSTANCE TimeStamp
LOCAL INSTANCE Values
LOCAL INSTANCE Keys
LOCAL INSTANCE Writes
LOCAL INSTANCE Reads
LOCAL INSTANCE Transactions
LOCAL INSTANCE ExecutionElem
LOCAL INSTANCE State
LOCAL INSTANCE Operation
LOCAL INSTANCE Transaction
LOCAL INSTANCE ReadState
LOCAL INSTANCE Execution
LOCAL INSTANCE ExecutionElems
LOCAL INSTANCE CT_SER
LOCAL INSTANCE CT_SSER
LOCAL INSTANCE SnapshotIsolation
LOCAL INSTANCE StrictSerializability
LOCAL INSTANCE ReadCommitted
LOCAL INSTANCE ReadUncommitted
LOCAL INSTANCE CheckTypes
LOCAL INSTANCE PrintT
LOCAL INSTANCE SerializabilityDebug
LOCAL INSTANCE Serializability

BEGIN

DEFINITIONS
  InitValue  -> _|_
  TimeStamp  -> _|_
  Values     -> _|_
  Keys       -> _|_
  Writes      -> _|_
  Reads       -> _|_
  Transactions -> _|_
  ExecutionElem -> _|_
  State -> _|_
  Operation -> _|_
  Transaction -> _|_
  ReadState -> _|_
  Execution -> _|_
  ExecutionElems -> _|_
  CT_SER -> _|_
  CT_SSER -> _|_
  SnapshotIsolation -> _|_
  StrictSerializability -> _|_
  ReadCommitted -> _|_
  ReadUncommitted -> _|_
  CheckTypes -> _|_
  PrintT -> _|_
  SerializabilityDebug -> _|_
  Serializability -> _|_
  TLA+Config -> _|_

END
====