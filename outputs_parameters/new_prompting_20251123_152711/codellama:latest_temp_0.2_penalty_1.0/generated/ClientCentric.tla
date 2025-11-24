---- MODULE ClientCentric ----
--------------------------------------------------------------------------------
(*

Client-Centric Isolation Specification

*)

CONSTANTS

\* The set of all possible keys
Keys == <<>>

\* The set of all possible values
Values == <<>>

\* The initial value for each key
InitValue == <<>>

\* The set of all transactions
Transactions == <<>>

\* The set of all read states
ReadStates == <<>>

\* The set of all write sets
WriteSets == <<>>

\* The set of all read-write sets
ReadWriteSets == <<>>

\* The set of all executions
Executions == <<>>

\* The set of all valid isolation levels
IsolationLevels == <<>>

\* The set of all valid commit tests
CommitTests == <<>>

\* The set of all valid read-write sets
ReadWriteSets == <<>>

\* The set of all valid read-only sets
ReadOnlySets == <<>>

\* The set of all valid write-only sets
WriteOnlySets == <<>>

\* The set of all valid read-write-only sets
ReadWriteOnlySets == <<>>

\* The set of all valid read-only-write sets
ReadOnlyWriteSets == <<>>

\* The set of all valid write-only-read sets
WriteOnlyReadSets == <<>>

\* The set of all valid read-write-only-read sets
ReadWriteOnlyReadSets == <<>>

\* The set of all valid write-only-read-write sets
WriteOnlyReadWriteSets == <<>>

\* The set of all valid read-only-write-read sets
ReadOnlyWriteReadSets == <<>>

\* The set of all valid write-only-read-write-read sets
WriteOnlyReadWriteReadSets == <<>>

\* The set of all valid read-write-only-read-write sets
ReadWriteOnlyReadWriteSets == <<>>

\* The set of all valid read-only-write-read-write sets
ReadOnlyWriteReadWriteSets == <<>>

\* The set of all valid write-only-read-write-read sets
WriteOnlyReadWriteReadSets == <<>>

\* The set of all valid read-write-only-read-write-read sets
ReadWriteOnlyReadWriteReadSets == <<>>

\* The set of all valid read-only-write-read-write-read sets
ReadOnlyWriteReadWriteReadSets == <<>>

\* The set of all valid write-only-read-write-read-read sets
WriteOnlyReadWriteReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read sets
ReadWriteOnlyReadWriteReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read sets
ReadOnlyWriteReadWriteReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read sets
WriteOnlyReadWriteReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadWriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid read-only-write-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
ReadOnlyWriteReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadSets == <<>>

\* The set of all valid write-only-read-write-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read-read sets
WriteOnlyReadWriteReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadReadRead
====