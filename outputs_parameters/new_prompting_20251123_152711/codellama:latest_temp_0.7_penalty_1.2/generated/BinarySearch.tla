---- MODULE BinarySearch ----
------------------------------ MODEL BinarySearch --------------------------
(*****************************************************************)
(* BEGIN TRANSLATION *)
END TRANSLATION
/\ Len(seq) \in Nat, <8>5
Modification History
Last modified Fri Feb 17 16:12:03 CET 2023 by merz
Last modified Tue Aug 27 12:59:52 PDT 2019 by loki
Last modified Fri May 03 16:28:58 PDT 2019 by lamport
Created Wed Apr 17 15:15:12 PDT 2019 by lamport
**************************************************************************)
--fair algorithm BinarySearch {
variables seq \in SortedSeqs, val \in Values,
low = 1, high = Len(seq), result = 0 ;
{ a: while (low =< high /\ result = 0) {
with (mid = (low + high) \div 2, mval = seq[mid]) {
if (mval = val) { result := mid}
else if (val < mval) { high := mid - 1}
else {low := mid + 1}                    } } } }
***************************************************************************)
Global variables *)
Allow infinite stuttering to prevent deadlock on termination. *)
**************************************************************************)
Partial correctness of the algorithm is expressed by invariance of      *)
formula resultCorrect.  To get TLC to check this property, we use a     *)
model that overrides the definition of Seq so Seq(S) is the set of      *)
sequences of elements of S having at most some small length.  For       *)
example,                                                                *)
*)
Seq(S) == UNION {[1..i -> S] : i \in 0..3}                           *)
*)
is the set of such sequences with length at most 3.                     *)
**************************************************************************)
**************************************************************************)
Proving the invariance of resultCorrect requires finding an inductive   *)
invariant that implies it.  A suitable inductive invariant Inv is       *)
defined here.  You can use TLC to check that Inv is an inductive        *)
invariant.                                                              *)
**************************************************************************)
Inv == (resultCorrect /\ low =< high) ==> result \in [1..high]
=============================================================================
====