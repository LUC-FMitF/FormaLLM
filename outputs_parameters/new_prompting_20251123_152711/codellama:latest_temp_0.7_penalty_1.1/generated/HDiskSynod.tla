---- MODULE HDiskSynod ----

(****************************************************************************)
(* Modification History                                                      *)
(****************************************************************************)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                       *)
(****************************************************************************)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                             *)
(****************************************************************************)
CONSTANTS   Inp,         \* The set of all inputs.
            Balance,     \* The set of all balances.
            TxId         \* The set of all transaction IDs.
VARIABLES   bk,          \* A bank account.
            tx,          \* The set of open snapshot transactions.
            written,     \* A log of writes performed within each transaction.
            missed       \* The set of writes invisible to each transaction.
------------------------------------------------------------------------------
NoVal ==    \* Choose something to represent the absence of a value.
    CHOOSE v : v \notin Inp

BkAcct ==    \* A bank account.
    [Balance -> INTEGER]

Store ==    \* The set of all key-value stores.
    [Key -> Val \cup {NoVal}]

Init == \* The initial predicate.
    /\ bk = BkAcct([b |-> 0])        \* The bank account starts with a balance of zero.
    /\ tx = {}                       \* The set of open transactions is initially empty.
    /\ written = [t \in TxId |-> {}] \* All write logs are initially empty.
    /\ missed = [t \in TxId |-> {}]  \* All missed writes are initially empty.
    
TypeInvariant ==    \* The type invariant.
    /\ bk \in BkAcct
    /\ tx \subseteq TxId
    /\ written \in [TxId -> SUBSET Key]
    /\ missed \in [TxId -> SUBSET Key]
    
TxLifecycle ==
    /\ \A t \in tx :                   \* If bk.bal != written & we haven't written it, we must have missed a write.
        \A k \in Balance : (bk[k] /= written[t][k] /\ k \notin written[t]) => k \in missed[t]
    /\ \A t \in TxId \ tx :            \* Checks transactions are cleaned up after disposal.
        /\ \A k \in Balance : bk[k] = 0
        /\ written[t] = {}
        /\ missed[t] = {}

OpenTx(t) ==    \* Open a new transaction.
    /\ t \notin tx
    /\ tx' = tx \union {t}
    /\ written'[t] = written[t]
    /\ missed'[t] = missed[t]
    /\ bk' = BkAcct([b |-> bk[b]])
    ==> (tx' = tx) /\ (written' = written) /\ (missed' = missed) /\ (bk' = bk)

Debit(i, t) ==                     \* Debits the bank account of the given amount.
    /\ i \in Inp
    /\ t \notin tx
    /\ tx' = tx \union {t}
    /\ written'[t] = written[t] \union {i}
    /\ missed'[t] = missed[t]
    /\ bk' = BkAcct([b |-> bk[b] - i])
    ==> (tx' = tx) /\ (written' = written) /\ (missed' = missed) /\ (bk' = bk)

Credit(i, t) ==                     \* Credits the bank account of the given amount.
    /\ i \in Inp
    /\ t \notin tx
    /\ tx' = tx \union {t}
    /\ written'[t] = written[t] \union {i}
    /\ missed'[t] = missed[t]
    /\ bk' = BkAcct([b |-> bk[b] + i])
    ==> (tx' = tx) /\ (written' = written) /\ (missed' = missed) /\ (bk' = bk)

Rollback(t) ==                      \* Rolls back the transaction.
    /\ t \in tx
    /\ tx' = tx - {t}
    /\ written'[t] = written[t]
    /\ missed'[t] = missed[t]
    /\ bk' = BkAcct([b |-> bk[b]])
    ==> (tx' = tx) /\ (written' = written) /\ (missed' = missed) /\ (bk' = bk)

CloseTx(t) ==                       \* Closes the transaction.
    /\ t \in tx
    /\ tx' = tx - {t}
    /\ written'[t] = written[t]
    /\ missed'[t] = missed[t]
    /\ bk' = BkAcct([b |-> bk[b]])
    ==> (tx' = tx) /\ (written' = written) /\ (missed' = missed) /\ (bk' = bk)

Spec == \* Initialize state with Init and transition with Next.
    Init /\ [](TypeInvariant /\ TxLifecycle)
------------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ TxLifecycle)
==============================================================================
====