---- MODULE HDiskSynod ----

(**************************************************************************)
(* Modification History                                                    *)
Last modified Sat Jan 26 15:53:08 CET 2019 by tthai
Created Sun Sep  7 14:24:08 CEST 2014 by thomas.hai
/\ (bk.bal = 0) \equiv (bk.inp = NotAnInput) *)
(***************************************************************************)
CONSTANTS Input, Output                                -- input and output values for the bank account system
          Balance                                     -- balance of the bank account
VARIABLES bk : {bal:Balance | 0 <= bal}              -- state variables (initially empty)
INITIALISATION
bk.inp = Input                             -- initial input value is set to "Input"
NEXT
/\ \A i, j: Nat | (i < j /\ bk[j].bal > 10) => FALSE   -- prevents an infinite loop by making sure that the balance of any bank account cannot be greater than $10$ at the same time as another bank account's.
\/                                              \* preventing two or more accounts from having a negative value at once is done using this formula, which also makes it impossible for there to ever be multiple banks with balances equal to zero (because we can then simply set bk[j].bal = 10). This means that even if one bank account has $5$ and another has $-2$, the second will always have a positive balance. *\/
\* prevents an infinite loop by making sure that two or more accounts cannot simultaneously be negative, which is done using this formula, as well as preventing there from ever being multiple banks with balances equal to zero (which can simply set bk[j].bal = 10). This means that even if one bank account has $5$ and another has $-2$, the second will always have a positive balance. *\/
\* The next-state relation                               \/
bk' = [i |-> { j: Nat| (bk[j].bal > 0 /\ bk[i] + bk[j].bal <= Balance) } ]   -- update state variables with new balances, making sure that the balance of any bank account cannot be greater than $10$ at the same time as another bank account's and prevents an infinite loop by making sure two or more accounts cannot simultaneously be negative.
\* The type invariant                                  \/
\/                      /\ (bk[i].bal > -Balance) => FALSE   -- prevents a balance from being less than $-$10, which would cause the bank to go into debt and make it impossible for there ever to be multiple banks with balances equal to zero. *\/
\* The output formula                              \/
/\ bk'[i].bal = Output  -- outputs a balance of $Output$, where $bk$ is updated according to the next-state relation above and any bank account that has an input value greater than its current balance will have its new balance set to equal this input. *\/
====