---- MODULE HDiskSynod ----
MODULE Banking

CONSTANTS
  Input,
  Output,
  Balance,
  Limit,
  Transaction,
  Deposit,
  Withdrawal

VARIABLES
  balance,
  limit,
  transactions

SPECIFICATION Spec

INVARIANTS
  Invariant1 ≡ balance ≤ limit
  Invariant2 ≡ transactions ≠ ∅

LOCAL INSTANCE Transaction

Transaction ≡
  [Input → Balance,
   Output → Balance,
   Balance → (Balance ∪ Limit),
   Limit → (Balance ∪ Limit),
   Transaction → (Balance ∪ Limit),
   Deposit → (Balance ∪ Limit),
   Withdrawal → (Balance ∪ Limit)]

Spec ≡
  Init ≡
    balance ← 0,
    limit ← 100,
    transactions ← ∅

Invariant1 ≡
  Init ≡
    balance ← 0,
    limit ← 100,
    transactions ← ∅

Transaction ≡
  [Input → Balance,
   Output → Balance,
   Balance → (Balance ∪ Limit),
   Limit → (Balance ∪ Limit),
   Transaction → (Balance ∪ Limit),
   Deposit → (Balance ∪ Limit),
   Withdrawal → (Balance ∪ Limit)]

Invariant2 ≡
  Init ≡
    balance ← 0,
    limit ← 100,
    transactions ← ∅

Transaction ≡
  [Input → Balance,
   Output → Balance,
   Balance → (Balance ∪ Limit),
   Limit → (Balance ∪ Limit),
   Transaction → (Balance ∪ Limit),
   Deposit → (Balance ∪ Limit),
   Withdrawal → (Balance ∪ Limit)]

END
====