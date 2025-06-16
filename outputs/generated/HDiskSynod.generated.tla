----------------- MODULE Bank -----------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT NotAnInput

VARIABLES bk, inp, out

TypeOK ==
/\ bk \in [bal: Int, inp: Seq(NotAnInput \cup Int), out: Seq(NotAnInput \cup Int)]
/\ inp \in Seq(NotAnInput \cup Int)
/\ out \in Seq(NotAnInput \cup Int)

Init ==
/\ bk = [bal |-> 0, inp |-> <<>>, out |-> <<>>]
/\ inp = <<>>
/\ out = <<>>

Next ==
\/ /\ inp /= <<>>
/\ bk' = [bk EXCEPT !.inp = Append(@, Head(inp)), !.bal = @ + Head(inp)]
/\ inp' = Tail(inp)
/\ out' = out
\/ /\ bk.inp /= <<>>
/\ bk' = [bk EXCEPT !.inp = Tail(@), !.out = Append(@, Head(@.inp))]
/\ inp' = inp
/\ out' = out

Spec ==
Init /\ [][Next]_<<bk, inp, out>>

Invariant ==
/\ (bk.bal = 0) <=> (bk.inp = <<>>)
/\ (bk.bal = 0) <=> (bk.out = <<>>)
/\ (bk.bal = 0) <=> (inp = <<>>)
/\ (bk.bal = 0) <=> (out = <<>>)
=============================================================================