---- MODULE ClientCentric ----

(***************************************************************************)
(* The module defines an initial state, a set of transactions, and a commit test. *)
(* It checks if the execution satisfies the commit test.                      *)
(***************************************************************************)

CONSTANT Keys == {1..5}
CONSTANT Values == {"red", "green", "blue"}
CONSTANT InitValue == "Init"

\* The initial state of the system.
State == [k \in Keys |-> InitValue]

(* A transaction is a total order of operations. *)
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* A helper function to determine if a transaction satisfies the commit test. *)
CT_SER(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

\* A helper function to determine if a transaction satisfies the commit test. *)
CT_SSER(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

\* A helper function to determine if a transaction satisfies the commit test. *)
CT_RU(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

\* A helper function to determine if a transaction satisfies the commit test. *)
CT_RU(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

\* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

\* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len == ZLen(transaction)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(execution, transaction, 0)

(* A helper function to determine if a transaction satisfies the commit test. *)
CT_RUC(transaction, execution) ==
  LET
    s1len == ZLen(execution)
    s2len ==
====