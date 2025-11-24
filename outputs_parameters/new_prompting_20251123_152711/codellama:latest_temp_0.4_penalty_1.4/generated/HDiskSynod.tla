---- MODULE HDiskSynod ----

(**********************************************)
(* Modification History                       *)
Last modified Sat Jan 26 15:52:41 CET 2019 by tthai
Created Sat Jan 26 15:23:57 CET 2019 by tthai
(/******************************)
(* BankAccount                   *)
(*********************************)
CONSTANTS NotAnInput, Withdrawal, Deposit \* Inputs to the bank account. *\/
INVARIANT (bk.bal = 0) ==> bk.inp = NotAnInput \* The initial balance is zero and there are no inputs yet.*\/
ACTION Init == /\ bk.bal = 0                        \* Initialize with a starting balance of $0. *\/
INITIALISATION Init
TRANSITION Invariant == (bk.inp = NotAnInput)       \* The initial input is not an actual transaction, so it has no effect on the account's state.*\/
ACTION Withdraw(a) == /\ bk.bal >= a                  \* A withdrawal of $a from the bank account. *\/
bk.inp = WITHDRAWAL(a);
bk.bal -= a;
TRANSITION Invariant == (bk.inp = NotAnInput)       \* The initial input is not an actual transaction, so it has no effect on the account's state.*\/
ACTION Deposit(d) == /\ bk.bal >= 0                   \* A deposit of $d into the bank account. *\/
bk.inp = DEPOSIT(d);
bk.bal += d;
TRANSITION Invariant == (bk.inp = NotAnInput)       \* The initial input is not an actual transaction, so it has no effect on the account's state.*\/
ACTION Transfer(a1, a2) == /\ bk.bal >= a1 + a2         \* A transfer of $a1 from one bank account to another ($a2). *\/
bk.inp = TRANSFER(a1, a2);
bk.bal -= a1;
bk.bal += a2;
TRANSITION Invariant == (bk.inp = NotAnInput)       \* The initial input is not an actual transaction, so it has no effect on the account's state.*\/
ACTION ClearInp == /\ bk.inp != Withdrawal           * A clearing of any pending inputs to the bank account. *\/
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearInp has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m) == /\ bk.bal >= 0                   * A printing of a message m and the current balance (bk.bal). *\/
Print("Current Balance: $", bk.bal);
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrints == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account. *\/
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrints has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintHelp(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintHelp has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* PrintBalance has printed out all input transactions, so it has no effect on the account's state.*\/
ACTION ClearAllInpsAndPrintsWithMessage(m1, m2, m3, m4) == /\ TRUE                   * A clearing of any pending inputs to and prints from the bank account with a message. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for the user to enter commands. *\/
Print("", bk.inp);
bk.bal = 0;                       \* The initial balance is zero and there are no inputs yet. *\/
TRANSITION Invariant == (bk.inp = NotAnInput)     \* ClearAllInpsAndPrintsWithMessage has cleared all input transactions, so it has no effect on the account's state.*\/
ACTION PrintBalance(m1, m2, m3, m4) == /\ TRUE                   * A printing of a message (m1), some help text about how to use this banking system (m2), another message (m3), and finally an invitation for
====