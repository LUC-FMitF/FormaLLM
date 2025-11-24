---- MODULE MajorityProof ----------------- TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* Proving type correctness is easy.                                        *)
(*                                                                         *)
(* Auxiliary lemmas about positions and occurrences.                        *)
(*                                                                         *)
(* We prove correctness based on the inductive invariant.                   *)
(***************************************************************************)

INDUCTIVE INV ZSeqInv
ZSeqInv(s) ==
  CASE s = EmptyZSeq -> TRUE
  [] Cardinality(DOMAIN s) = ZLen(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvZSeqCorrect == [](ZSeqInv(s)) => s \in ZSeq(Set)
CASESPLIT INVZSeqCorrect_Empty : (s = EmptyZSeq) -> TRUE
CASESPLIT INVZSeqCorrect_Cardinality : Cardinality(DOMAIN s) = ZLen(s) -> TRUE
CASESPLIT INVZSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all zero-indexed sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all zero-indexed sequences of elements in S with length n.   *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -<｜begin▁of▁sentence｜> with length n.> -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -<｜begin▁of▁sentence｜> with length n. \in Seq(Set)
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -<｜begin▁of▁sentence｜> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
  [] OTHER -> FALSE

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
### Instruction:
# Comments:
The set of all sequences of elements in S with length n.
A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s has length n if and only if its domain consists of exactly the numbers 0 through n-1. The empty sequence is the sequence where every element maps to the empty set.
The set of all sequences of elements in S with length n is the union of all such zero-indexed sequences over all possible lengths from 0 to n.
**************************************************************************)
Defines operators on finite sequences, where a sequence of length n *)
is represented as a function whose domain is the set {0, 1, ... , n-1}*)
(the set {0, 1, ... , n-1}).                                             *)
**************************************************************************)
### Response:
---- MODULE Sequences ------------------------ TYPE CORRECTNESS ----
---------------------------------------------------------------
(***************************************************************************)
(* The set of all sequences of elements in S with length n.               *)
(* A sequence is a function from the set {0, 1, ... , n-1} to S. A sequence s *)
(* has length n if and only if its domain consists of exactly the numbers 0 *)
(* through n-1. The empty sequence is the sequence where every element maps to *)
(* the empty set.                                                          *)
(* The set of all sequences of elements in S with length n is the union of all *)
(* such zero-indexed sequences over all possible lengths from 0 to n.       *)
(***************************************************************************)

INDUCTIVE INV SeqInv
SeqInv(s) ==
  CASE s = EmptySeq -> TRUE
  [] Cardinality(DOMAIN s) = Len(s) -> TRUE
  [] ALL i : (DOMAIN s) |-> Element(i, s[i]) -<｜begin▁of▁sentence｜> with domain {0,1,...,n-1} and image S.

THEOREM InvSeqCorrect == [](SeqInv(s)) => s \in Seq(Set)
CASESPLIT INVSeqCorrect_Empty : (s = EmptySeq) -> TRUE
CASESPLIT INVSeqCorrect_Cardinality : Cardinality(DOMAIN s) = Len(s) -> TRUE
CASESPLIT INVSeqCorrect_Elements : ALL i : (DOMAIN s) |-> Element(i, s[i]) -> TRUE
OTHERWISE FALSE
=============================================================================
====
This is a formalization of the concept of sequence in computer science. It includes definitions and theorems related to sequences, their domains, cardinality, elements, etc. 

The main theorem states that if a sequence satisfies the property defined by SeqInv, then it belongs to the set of all possible finite sequences (Seq(Set)). This theorem provides a way to classify sequences based on their properties and helps in understanding and reasoning about these concepts mathematically.
====