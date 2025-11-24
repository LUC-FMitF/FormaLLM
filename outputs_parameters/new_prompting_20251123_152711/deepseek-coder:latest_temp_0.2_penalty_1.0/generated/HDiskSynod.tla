---- MODULE HDiskSynod ----
MODULE BankAccount

CONSTANTS
  Balance,
  Input,
  NotAnInput

VARIABLES
  bk : BankAccount  -- The bank account

INITIAL
  bk  -- The initial state of the bank account

TRANSACTIONAL_OPERATIONS
  UpdateBalance(delta) :
    IF bk.Balance + delta > 0
    THEN bk.Balance ← bk.Balance + delta
    ELSE bk.Balance ← 0

  UpdateInput(newInput) :
    IF newInput ≠ bk.Input
    THEN bk.Input ← newInput

SPECIFICATION
  Initially(bk.Balance = 0, bk.Input = NotAnInput)
  After(UpdateBalance(10), bk.Balance = 10, bk.Input = NotAnInput)
  After(UpdateInput("New Input"), bk.Balance = 10, bk.Input = "New Input")
====