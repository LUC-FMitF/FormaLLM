---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History                                                     *)
(***************************************************************************)

CONSTANTS   Inp,    \* The set of all inputs.
            Bal,    \* The set of all balances.
            TxId    \* The set of all transaction IDs.
VARIABLES   bk,     \* A bank account with balance and input.
            tx      \* The set of open snapshot transactions.
            written \* A log of writes performed within each transaction.
-----------------------------------------------------------------------------
NoInp ==    \* Choose something to represent the absence of an input.
    CHOOSE i : i \notin Inp

Balance ==   \* The set of all balances.
    [b \in Bal |-> 0]

BankAccount == \* A bank account with balance and input.
    [bk = b, inp = NoInp]

Init == \* The initial predicate.
    /\ bk = BankAccount
    /\ tx = {}                              \* The set of open transactions is initially empty.
    /\ written = []                         \* All write logs are initially empty.
    
TypeInvariant ==    \* The type invariant.
    /\ bk \in Balance
    /\ tx \subseteq TxId
    /\ written \in [TxId -> SUBSET Inp]
    
TxLifecycle ==
    /\ \A t \in tx :                        \* If balance != snapshot & we haven't written it, we must have missed a write.
        \A i \in Inp : (bk[i] /= written[t][i] /\ i \notin written[t]) => i \in Missed(t)
    /\ \A t \in TxId \ tx :                 \* Checks transactions are cleaned up after disposal.
        /\ bk = BankAccount
        /\ written[t] = []
    
OpenTx(t) ==    \* Open a new transaction.
    /\ t \notin tx
    /\ tx' = tx \cup {t}
    /\ UNCHANGED <<bk, written>>

Deposit(t, i, v) ==  \* Using transaction t, deposit value v into the account under input i.
    /\ t \in tx
    /\ bk[i] = Balance[v]
    /\ written' = [written EXCEPT ![t][i] = @ \cup {i}]
    /\ UNCHANGED <<tx, Missed(t)>>
    
Withdraw(t, i, v) ==  \* Using transaction t, withdraw value v from the account under input i.
    /\ t \in tx
    /\ bk[i] = Balance[-v]
    /\ written' = [written EXCEPT ![t][i] = @ \cup {i}]
    /\ UNCHANGED <<tx, Missed(t)>>
    
RollbackTx(t) ==  \* Using transaction t, roll back the account to its state before the transaction began.
    /\ t \in tx
    /\ bk = BankAccount
    /\ written[t] = []
    /\ UNCHANGED <<tx, Missed(t)>>
    
CloseTx(t) ==  \* Using transaction t, close the account and discard any uncommitted changes.
    /\ t \in tx
    /\ bk = BankAccount
    /\ written[t] = []
    /\ UNCHANGED <<tx, Missed(t)>>
    
Spec == \* Initialize state with Init and transition with Next.
    Init /\ [][Next]_<<bk, tx, written>>
=============================================================================
====