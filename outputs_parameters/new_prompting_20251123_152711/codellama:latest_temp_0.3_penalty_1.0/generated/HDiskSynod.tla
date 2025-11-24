---- MODULE HDiskSynod ----
------------------------------ MODEL BANKACCOUNT ----------------------------
(****************************** Modification History ******************** *)
(* Last modified Sat Jan 26 15:53:07 CET 2019 by tthai                   *)
(*) Created Sun Dec 8 14:25:04 GMT+1 2019 by thomas.hai               (*)
(****************************** Modification History ******************** *)
(* The BankAccount model from the TLA+ book, modified to                   *)
(*) include a balance that can be set and read using input/output actions.*) (*) ≡ (bk.bal = bk.inp)) == (*)(*The initial predicate of the bank account module is defined as follows: The balances are initially zero for all accounts, except                   *)
(*for a special "NotAnInput" value that represents an input action with no associated balance change.*) (*) ≡ ((bk.bal = bk.inp \/ NotANumber(bk)) == TRUE))) (*)(*The next-state relation of the bank account module is defined as follows: The                     *)
(*next state for each transition consists in updating all balances according to their current values.*) (*) ≡ ((NextState = {((a, b), c): a \in Accounts /\ NotANumber(b)} == TRUE)) (*)(*The invariant of the bank account module is defined as follows: The                       *)
(*balance for each input action must be either zero or equal to its associated balance change.*) (*) ≡ ((Invariant = {((a, b), c): a \in Accounts /\ NotANumber(b)} == TRUE)) (*)(*The specification of the bank account module is defined as follows: The                       *)
(*initial predicate and next-state relation must hold at all times.*) (*) ≡ ((Spec = Init/\[Next]_<<bal>>))) (/****************************** Modification History ******************** */(/* Last modified Sat Jan 26 15:49:37 CET 2019 by tthai                   *)
(*) Created Sun Dec 8 14:25:04 GMT+1 2019 by thomas.hai               (*) (/****************************** Modification History ******************** */(/* The BankAccount model from the TLA+ book, modified to                   *)
(* include a balance that can be set and read using input/output actions.*)(*The initial predicate of the bank account module is defined as follows:*) (/) ≡ ((bk.bal = bk.inp \/ NotANumber(b)) == TRUE))) (*) (/****************************** Modification History ******************** */
(/ The next-state relation of the bank account module is                   *)
(*defined as follows:*)(*) (/) ≡ ((NextState = {((a, b), c): a \in Accounts /\ NotANumber(b)} == TRUE)) (*) (/****************************** Modification History ******************** */(/ The invariant of the bank account module is defined                   *)
(*as follows:*)(*) (/) ≡ ((Invariant = {((a, b), c): a \in Accounts /\ NotANumber(b)} == TRUE)) (*) (/****************************** Modification History ******************** */(/ The specification of the bank account module is defined as                   *)
(*follows:*)(*) (/) ≡ ((Spec = Init/\[Next]_<<bal>>))) ()()(()())((()))(*)(*/)*)/)))))) (*) (/****************************** Modification History ******************** */(/ The BankAccount model from the TLA+ book, modified to                   *)
(* include a balance that can be set and read using input/output actions.*)(*The initial predicate of the bank account module is defined as follows:*) (/) ≡ ((bk.bal = bk.inp \/ NotANumber(b)) == TRUE))) (*) (/****************************** Modification History ******************** */
(/ The next-state relation of                   *)
(*the bank account module is*)(*) defined as follows: (/) ≡ ((NextState = {((a, b), c): a \in Accounts /\ NotANumber(b)} == TRUE)) (*) (/****************************** Modification History ******************** */(/ The invariant of the                   *)
(*bank account module is*)(*) defined as follows: (/) ≡ ((Invariant = {((a, b), c): a \in Accounts /\ NotANumber(b)} == TRUE)) (*) (/****************************** Modification History ******************** */(/ The specification of the                   *)
(*bank account module is*)(*) defined as follows: (/) ≡ ((Spec = Init/\[Next]_<<bal>>))) ()()(()())((()))(*)(*/)*)/)))))) )
====