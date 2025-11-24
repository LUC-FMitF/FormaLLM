---- MODULE HDiskSynod ----

(**********************************************************************************)
(* Modification History                                                             *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                                *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                                      *)
(**********************************************************************************)

EXTENDS ZSequences
CONSTANTS   NotAnInput,     \* Represents a state where there is no valid input.
            MinInt          \* The smallest possible integer value for balance.
VARIABLES   bk              \* BankAccount instance variables.
            bal,             \* Account balance.
            inp             \* Last valid input received from user.

(* A bank account has a non-negative balance and can either receive an amount of money or *)
(* transfer the full amount of its balance to another account.                            *)
LOCAL OPERATIONS 
    Deposit(x) == IF x \geq 0 THEN bal + x ELSE bal END,
    Transfer(x) == IF x \leq bal AND x \geq 0 THEN bal - x ELSE bal END;

Init == 
    /\ bk.bal = 0              \* Initial balance is zero.
    /\ bk.inp = NotAnInput     \* No valid input has been received at the start.

Next == 
    /\  EXISTS x : Transfer(x)
    /\  EXISTS y : Deposit(y)
    /\  OTHERWISE Unchanged

SPECIFICATION Spec == Init /\ [](bk.bal >= 0) /\ ([bk.inp = NotAnInput] -> bk.bal = 0)
INVARIANT TypeOK == 
    /\ (bk.bal \geq MinInt)  \* Account balance must be non-negative.
    /\ ((bk.inp = Deposit(x)) -> x >= 0)      \* If input is deposit, amount should be positive.
    /\ ((bk.inp = Transfer(y)) -> y <= bk.bal)  \* If input is transfer, amount should not exceed balance.
====