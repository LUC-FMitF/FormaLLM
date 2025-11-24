---- MODULE HDiskSynod ----

(***************************************************************************)
(* Modification History                                                     *)
(***************************************************************************)

(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai *)

CONSTANTS
  Inp,     \* The set of all inputs.
  Out,     \* The set of all outputs.
  Bal,     \* The set of all balances.
  NotAnInput, \* A special value to represent an invalid input.
  NoOutput, \* A special value to represent an invalid output.
  NoBalance, \* A special value to represent an invalid balance.
VARIABLES
  bk,      \* The bank account.
  inp,     \* The input.
  out,     \* The output.
  bal,     \* The balance.
INIT
  bk = [
    inp = Inp,
    out = Out,
    bal = Bal
  ]

Next ==
  \/ \E inp \in Inp :
    \/ \E out \in Out :
      \/ \E bal \in Bal :
        \/ (bk.inp = inp /\ bk.out = out /\ bk.bal = bal)
        \/ (bk.inp = NotAnInput /\ bk.out = NoOutput /\ bk.bal = NoBalance)

Spec ==
  Init /\ [][Next]_<<bk, inp, out, bal>>

INVARIANTS
  TypeOK

TypeOK ==
  /\ bk.inp \in Inp
  /\ bk.out \in Out
  /\ bk.bal \in Bal

TLCConfig ==
CONSTANTS
  Inp,     \* The set of all inputs.
  Out,     \* The set of all outputs.
  Bal,     \* The set of all balances.
  NotAnInput, \* A special value to represent an invalid input.
  NoOutput, \* A special value to represent an invalid output.
  NoBalance, \* A special value to represent an invalid balance.
VARIABLES
  bk,      \* The bank account.
  inp,     \* The input.
  out,     \* The output.
  bal,     \* The balance.
INIT
  bk = [
    inp = Inp,
    out = Out,
    bal = Bal
  ]

Next ==
  \/ \E inp \in Inp :
    \/ \E out \in Out :
      \/ \E bal \in Bal :
        \/ (bk.inp = inp /\ bk.out = out /\ bk.bal = bal)
        \/ (bk.inp = NotAnInput /\ bk.out = NoOutput /\ bk.bal = NoBalance)

Spec ==
  Init /\ [][Next]_<<bk, inp, out, bal>>

INVARIANTS
  TypeOK

TypeOK ==
  /\ bk.inp \in Inp
  /\ bk.out \in Out
  /\ bk.bal \in Bal

=============================================================================
====