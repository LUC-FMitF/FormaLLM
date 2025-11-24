---- MODULE KVsnap ----
(***************************************************************************)
(* Defines operators for a simple key-value store with snapshot isolation  *)
(* This version has atomic updates of store and missed sets of txns       *)
(***************************************************************************)
CONSTANTS Key,            \* The set of all keys.                        *)
          TxId,           \* The set of all transaction IDs.              *)
          NoVal;         { Choose something to represent the absence of  *}
{ a value.}             \* All key-value stores have this initial state.*)
VARIABLES store,            \* A data store mapping keys to values.      *)
          tx,               \* The set of open snapshot transactions.    *)
          missed;           \* The set of writes invisible to each       *}
{ transaction.}             {transaction}.                                }
-----------------------------------------------------------------------------
NoVal ==    \* Choose something to represent the absence of a value.   *)
  CHOOSE v : v \notin Val

Store ==    \* The set of all key-value stores.                        *)
{ A data store mapping keys to values.}                {A data store *}
\* Mapping from each transaction ID to the writes it missed.*)
Missed(t, k) = 1 if t has written value v for key k and that write is invisible in tx; otherwise Missed(t,k)=0. *)
-----------------------------------------------------------------------------
STUTTERING ON INFINITE TIME                   {Infinite stuttering *}
{to prevent deadlock on termination.}        \* Global variables }
Process t = 1 if transaction is active; otherwise Process(t) = 0. *)
-----------------------------------------------------------------------------
FAIRNESS INVARIANTS                          {Fairness invariants   *}
{to ensure that all transactions are executed fairly.}         \* Algorithm }
KVsnap() == [
START:     \* Start the transaction                *)
tx := tx \union {self};
store := store;  \* take my snapshot of store      *)
with (rk \in SUBSET Key \ { {} }; wk \in SUBSET Key \ { {} }) {
read_keys := rk;     \* select a random read-key-set from possible *}
{read keys for the transaction.}                           }
READ:      \* Process reads on my snapshot        *)
log reads for CC isolation check
ops := ops \o SetToSeq({rOp(k, store[k]): k \in read_keys});  {Process *}
UPDATE:    \* Process writes on my snapshot       *)
store := [k \in Key |-> IF k \in write_keys THEN self ELSE store[k] ];   }
{write 'self' as value.}                              {writes for the*}
COMMIT:     \* Commit the transaction to the database if there is no *}
if (missed(self, w) = 0; otherwise take self off of active txn set and update store. *)
{conflict.}            }
UPDATE_MISSING:   {Update missed writes for other open transactions.*}
missed := [o \in TxId |-> IF o \in tx THEN missed[o] \union write_keys ELSE missed[o]];  }
update store;                     {and update the store.}            }
log reads for CC isolation check       *}
ops := ops \o SetToSeq({wOp(k, self): k \in w});        {Processing*}
{writes for the transaction.*}                }             ]         *)
-----------------------------------------------------------------------------
INVARIANTS                          {Invariants to ensure that *}
KVsnap() == [  \* The store and missed sets are consistent.      *)
store = [k |-> IF k \in Key THEN (IF tx \union {self} IN Missed(t, k) THEN self ELSE NoVal)]];   }
\* All transactions have been executed.*                           *}
tx == {};  \* The set of open snapshot transactions is empty.       *)
-----------------------------------------------------------------------------
BEGIN TRANSLATION (chksum(pcal) = "1adfcb46" /\ chksum(tla) = "5b28617f") END *}
{Translation of PlusCal algorithm to TLA+.*                          }
-----------------------------------------------------------------------------
Snapshot isolation invariant                {Invariant for snapshot   *)
isolation.                      \* guarantees that all transactions  *}
\* are executed fairly and with consistent results.}             {results.}
{All writes in a transaction must be visible to other          }
transactions before they commit, otherwise there is        {a conflict.*}
race condition. The missed set of each           }                      \*}
transaction contains all the keys that were written       *}
by that transaction and are invisible         {in some other    *}
{to it.}                              transactions; this ensures  {transactions}.
-----------------------------------------------------------------------------
TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Seq = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *}
\* All transactions have been executed.*                           {results.}    TYPE Set = << >> ;            \* The set of integers.               *)
Key == [k |-> IF k \in Key THEN (IF tx IN Missed(t, k) THEN self ELSE NoVal)]];   } *
====