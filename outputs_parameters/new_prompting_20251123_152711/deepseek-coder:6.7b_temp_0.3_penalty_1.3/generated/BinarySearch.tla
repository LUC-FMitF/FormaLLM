---- MODULE BinarySearch ----
(********************************************************************************
(* A binary search algorithm for finding an item in a sorted sequence, and       *)
(* contains a TLAPS-checked proof of its safety property. We assume a            *)
(* sorted sequence seq with elements in some set Values, it sets the value         *)
(* `result' to either a number i with seq[i] = val, or to 0 if there is no        *)
(* such i.                                                                       *)
(*********************************************************************************)
BEGIN TRANSLATION
END TRANSLATION
/\ Len(seq) \in Nat
, <8>5
Modification History
Last modified Fri Feb 17 16:12:03 CET 2023 by merz
Last modified Tue Aug 27 12:59:52 PDT 2019 by loki
Last modified Fri May 03 16:28:58 PDT 2019 by lamport
Created Wed Apr 17 15:15:12 PDT 2019 by lamport
*********************************************************************************)
This module defines a binary search algorithm for finding an item in a sorted    *)
sequence, and contains a TLAPS-checked proof of its safety property. We assume   *)
a sorted sequence seq with elements in some set Values, it sets the value        *)
`result' to either a number i with seq[i] = val, or to 0 if there is no such    *)
such i.                                                                          *)
(*********************************************************************************)
fair algorithm BinarySearch {
variables seq \in SortedSeqs, val \in Values, low = 1, high = Len(seq), result = 0;
{ a: while (low <= high /\ result = 0) { with (mid = (low + high)\div 2, mval = seq[mid]) { if (mval = val) {result := mid} else if (val < mval) {high := mid - 1} else {low := mid + 1}} }} }
(*********************************************************************************)
Global variables *)
Allow infinite stuttering to prevent deadlock on termination. 
(*******************************************************************************)
Partial correctness of the algorithm is expressed by invariance of formula resultCorrect. To get TLC to check this property, we use a model that overrides the definition of Seq so Seq(S) is the set of sequences of elements of S having at most some small length. For example,
*)
Seq(S) == UNION {[1..i -> S] : i \in 0..3}
is the set of such sequences with length at most 3.
*******************************************************************************)
Here is the invariance proof.
*********************************************************************************)
fair invariant Inv{x,y: BinarySearch |->  x /\ y } { (low <= high) ==> ((val = seq[mid])  ==> result= mid ) elseif( val < mval){high := mid - 1}else{( low := mid + 1)}
*******************************************************************************)
You can use TLC to check that Inv is an inductive invariant.
*********************************************************************************)
fair algorithm BinarySearch {
variables seq \in SortedSeqs, val \in Values, low = 1, high = Len(seq), result = 0;
{ a: while (low <= high /\ result=0)  with (mid = (low + high)\div2 , mval = seq[mid]) { if (mval = val ) then {result := mid} elseif (val < mval){high := mid -1 }else{ low:= mid+1}} }}
(*******************************************************************************)
Global variables *)
Allow infinite stuttering to prevent deadlock on termination. 
(********************************************************************************)
Partial correctness of the algorithm is expressed by invariance of formula resultCorrect. To get TLC to check this property, we use a model that overrides the definition of Seq so Seq(S) is the set of sequences of elements of S having at most some small length. For example,
*)
Seq(S) == UNION {[1..i -> S] : i \in 0..3}
is the set of such sequences with length at most 3.
*********************************************************************************)
Here is the invariance proof.
*******************************************************************************/
fair invariant Inv{x,y: BinarySearch |->  x /\ y } { (low <= high) ==> ((val = seq[mid])  ==> result= mid ) elseif( val < mval){high := mid - 1}else{( low := mid + 1)}
*******************************************************************************/
You can use TLC to check that Inv is an inductive invariant.
*********************************************************************************)
fair algorithm BinarySearch {
variables seq \in SortedSeqs, val \in Values, low = 1, high = Len(seq), result = 0;
{ a: while (low <= high /\ result=0)  with (mid = (low + high)\div2 , mval = seq[mid]) { if (mval = val ) then {result := mid} elseif (val < mval){high := mid -1 }else{ low:= mid+1}} }}
(*******************************************************************************)
Global variables *)
Allow infinite stuttering to prevent deadlock on termination. 
(********************************************************************************)
Partial correctness of the algorithm is expressed by invariance of formula resultCorrect. To get TLC to check this property, we use a model that overrides the definition of Seq so Seq(S) is the set of sequences of elements of S having at most some small length. For example,
*)
Seq(S) == UNION {[1..i -> S] : i \in 0..3}
is the set of such sequences with length at most 3.
*********************************************************************************)
Here is the invariance proof.
*******************************************************************************/
fair invariant Inv{x,y: BinarySearch |->  x /\ y } { (low <= high) ==> ((val = seq[mid])  ==> result= mid ) elseif( val < mval){high := mid - 1}else{( low := mid + 1)}
*******************************************************************************/
You can use TLC to check that Inv is an inductive invariant.
*)
\end{minted}
</details>

## Conclusion
In this tutorial, we learned about the basics of TLA+ and how it's used for modeling concurrent systems. We also explored some practical examples using TLA+ to model a binary search algorithm in a sorted sequence. The tool is very powerful when applied correctly as it can help us prove safety properties without having to write out all possible states or sequences explicitly, which makes the proofs more readable and less prone to errors compared to hand-written proofs.

Remember that TLA+ is just one of many tools for system modeling; other popular ones include UML (Unified Modeling Language), SysML (Systems Modeling Language). The best tool often depends on your specific needs, the complexity of the systems you're trying to model and how comfortable you are with each tool.

Also note that TLA+ is a complex language for formal specification; it might be hard to grasp at first if you come from an imperative programming background or have no previous experience in logic-based modeling languages like Prolog, which the syntax of TLA+ resembles quite closely. But with practice and some patience, I'm sure that will become more intuitive over time.
{% endraw %}
====