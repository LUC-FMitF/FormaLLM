---- MODULE HDiskSynod ----
MODULE BankingSystem

CONSTANTS
  Balance,
  Input,
  Output,
  NotAnInput,
  TransactionFee,
  MinimumTransactionAmount,
  MaximumTransactionAmount

VARIABLES
  balance,
  transactions,
  input,
  output,
  pendingTransactions

SPECIFICATION

INVARIANT
  balance ∈ Naturals
  transactions ∈ Sequences
  input ∈ Sequences
  output ∈ Sequences
  pendingTransactions ∈ Sequences

BEGINNING
  balance = MinimumTransactionAmount
  transactions = {}
  input = NotAnInput
  output = {}
  pendingTransactions = {}

OPERATIONS

Operation(bk, inp, outp) ⇒ balance ≠ MaximumTransactionAmount
  IF input ≠ NotAnInput
  THEN balance = balance + inp
  ELSE balance = balance - outp

Transaction(bk, inp, outp) ⇒ Operation(bk, inp, outp)
  IF balance ≠ MinimumTransactionAmount
  THEN balance = balance - TransactionFee
  ELSE IF input ≠ NotAnInput
  THEN transactions = transactions ∪ {inp}
  ELSE output = output ∪ {outp}

Input(bk, inp) ⇒ Operation(bk, inp, 0)
  IF input ≠ NotAnInput
  THEN input = input + inp
  ELSE input = input - 0

Output(bk, outp) ⇒ Operation(bk, 0, outp)
  IF output ≠ {}
  THEN output = output ∪ {outp}
  ELSE output = output ∪ {0}

PendingTransaction(bk, inp, outp) ⇒ Transaction(bk, inp, outp)
  IF pendingTransactions ≠ {}
  THEN pendingTransactions = pendingTransactions ∪ {inp}
  ELSE pendingTransactions = pendingTransactions ∪ {outp}

END

THEOREM
  INVARIANT ⇒
    {balance ≠ MaximumTransactionAmount}
    {transactions ∈ Sequences}
    {input ∈ Sequences}
    {output ∈ Sequences}
    {pendingTransactions ∈ Sequences}
END
====