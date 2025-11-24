---- MODULE BankAccount 
------------------------------ MODULE HDiskSynod ----------------------------

CONSTANTS 
  NotAnInput,
  InitialBalance = 0;

VARIABLES 
  bk == <<Balance: InitialBalance, Input: NotAnInput>>;

ASSIGN 
  NextBalance(bk) == IF bk.Input = NotAnInput THEN bk.Balance ELSE bk.Input,
  NextInput(bk) == IF bk.Input = NotAnInput THEN bk.Input ELSE NotAnInput;

INVARIANTS 
  TypeOK == <<Balance: NATURAL, Input: {NotAnInput} U NATURAL>> SUBSET DOMAIN bk,
  BalanceOK == bk.Balance >= 0,
  InputOK == bk.Input = NotAnInput OR bk.Input IN NATURAL;

SPECIFICATION 
  Init == bk = <<Balance: InitialBalance, Input: NotAnInput>>,
  Next == bk.Balance = NextBalance(bk),
  bk.Input = NextInput(bk);

TLC Configuration:
CONSTANTS 
  NotAnInput = 0,
  InitialBalance = 0;

SPECIFICATION 
  Spec == Init /\ [](BalanceOK /\ InputOK);

INVARIANTS 
  TypeOK,
  BalanceOK,
  InputOK;

====