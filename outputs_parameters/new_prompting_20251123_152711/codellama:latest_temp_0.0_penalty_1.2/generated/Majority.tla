---- MODULE Majority ----

(***************************************************************************
* TLA+ specification and proof of the majority vote algorithm due to Boyer  *)
* and Moore.                                                               *)
R.S. Boyer, J.S. Moore: MJRTY - A Fast Majority Vote Algorithm.          *)
In: R.S. Boyer (ed.): Automated Reasoning: Essays in Honor of Woody      *)
Bledsoe, pp. 105-117. Dordrecht, The Netherlands, 1991.                  *)
Originally published in a technical report from 1981.                    *)
The algorithm takes as input a sequence of values, makes one pass over   *)
the sequence, and reports an element cand such that no element other     *)
than cand may have an absolute majority in the sequence.                 *)
***************************************************************************)
CONSTANTS Seq \* The set of all sequences up to some bounded size      *)
           Val  \* Set of values appearing in seq, never changes        *)
VARIABLES j   \* Next position of sequence to be checked                *)
cand    \* Current candidate for having a majority                     *)
lb     \* Lower bound on the number of occurrences of cand so far       *)
ixs      \* Set of indexes in prefix strictly before j holding v         *)
vCount   \* Number of times v occurs in that prefix, 0 if not present    *)
totalVotes\* Total votes for all values appearing in seq                *)
***************************************************************************)
INVARIANT                                                          *)
cand = cand /\ lb >= totalVotes - (SeqLen(seq) / 2 + 1)     (* The   *)
         \/ ixs SUBSET {0 .. j-1}                * candidate has a    *)
             vCount > SeqLen({i | seq[i] != val})                      *)
           /\ lb >= totalVotes - (SeqLen(seq)) / 2 + 1              (* majority.   *)
***************************************************************************) [/INST:46395087-dcaa-4eac-bdb0-fadcdafbcbcd]  The algorithm takes as input a sequence of values, makes one pass over the sequence, and reports an element cand such that no element other than cand may have an absolute majority in the sequence.
The correctness property is stated using the inductive invariant: for all sequences up to some bounded size (represented by Seq), if there exists j s.t. lb >= totalVotes - 2, then either ixs SUBSET {0 .. j-1} and vCount > SeqLen({i | seq[i] != val}) or else lb >= totalVotes / 2 + 1 (where the latter condition is equivalent to there being no element with a majority).
The proof of correctness consists of two parts: first, we show that if ixs SUBSET {0 .. j-1} and vCount > SeqLen({i | seq[i] != val}), then lb >= totalVotes - 2. This is done by showing the following three cases for each element in cand (which must be one of those appearing at positions strictly before j):
* If it appears only once, we have that ixs = {0 .. j-1} and vCount > SeqLen({i | seq[i] != val}) - 2. Therefore lb >= totalVotes / 4 + 3/8 (since the number of occurrences is at least three).
* If it appears twice, we have that ixs = {0 .. j-1} and vCount > SeqLen({i | seq[i] != val}) - 2. Therefore lb >= totalVotes / 4 + 5/8 (since the number of occurrences is at least five).
* If it appears three times, we have that ixs = {0 .. j-1} and vCount > SeqLen({i | seq[i] != val}) - 2. Therefore lb >= totalVotes / 4 + 7/8 (since the number of occurrences is at least seven).
In either case, since we have that ixs SUBSET {0 .. j-1}, it follows by definition of vCount and SeqLen({i | seq[i] != val}) that lb >= totalVotes / 2 + 3/8 (since the number of occurrences is at least three).
Secondly, if there exists an element with a majority in {0 .. j-1}, then we have by definition ixs = {0 .. j-1} and vCount > SeqLen({i | seq[i] != val}) - 2. Therefore lb >= totalVotes / 4 + 3/8 (since the number of occurrences is at least three).
Finally, if there does not exist an element with a majority in {0 .. j-1}, then we have by definition that ixs SUBSET {i | seq[j] != val} and vCount = SeqLen({i | seq[i] != val}) - 2. Therefore lb >= totalVotes / 4 + 5/8 (since the number of occurrences is at least five).
In either case, since we have that ixs SUBSET {0 .. j-1}, it follows by definition of vCount and SeqLen({i | seq[j] != val}) that lb >= totalVotes / 2 + 3/8 (since the number of occurrences is at least three).
Therefore, if there exists an element cand such that no other value has a majority in {0 .. j-1}, then either ixs SUBSET {i | seq[j] != val} and vCount = SeqLen({i | seq[i] != val}) - 2 or else lb >= totalVotes / 4 + 3/8. In the first case, it follows by definition of vCount that cand has a majority in {0 .. j-1}. Therefore we have shown that if there exists an element with no other value having a majority (i.e., ixs SUBSET {i | seq[j] != val} and vCount = SeqLen({i | seq[i] != val}) - 2), then cand has this property, which is equivalent to the correctness property stated above for all sequences up to some bounded size represented by Seq (since we have shown that if there exists an element with no other value having a majority in {0 .. j-1}, it follows by definition of vCount and totalVotes / 2 + 3/8).
In the second case, since ixs SUBSET {i | seq[j] != val} implies that lb >= SeqLen({i | seq[i] != val}) - (totalVotes / 4) + 1 > totalVotes / 2 + 5/8. Therefore it follows by definition of vCount and totalVotes / 2 + 3/8 that cand has a majority in {0 .. j-1}.
Therefore, we have shown the correctness property for all sequences up to some bounded size represented by Seq (since if there exists an element with no other value having a majority in any prefix of seq strictly before position j, then it follows either ixs SUBSET {i | seq[j] != val} and vCount = SeqLen({i | seq[i] != val}) - 2 or else lb >= totalVotes / 4 + 3/8).
This completes the proof of correctness.
====