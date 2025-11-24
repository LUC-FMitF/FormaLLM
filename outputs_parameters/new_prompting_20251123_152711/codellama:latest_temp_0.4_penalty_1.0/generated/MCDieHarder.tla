---- MODULE MCDieHarder ----

(**************************************************************************)
(* The following definitions duplicate the original Die Hard problem.     *)
(**************************************************************************)

CONSTANTS Goal     \* The goal state.
    \* The set of all possible values of Jug.
    Jug      <- {1, 2, 3}
    \* The set of all possible values of Capacity.
    Capacity <- {1, 2, 3}

Spec ==
    \* The initial state is the empty sequence.
    []
    \* The goal state is a sequence of length Goal.
    \/ \A s \in ZSeq(Jug) : ZLen(s) = Goal

Init ==
    \* The initial state is the empty sequence.
    []

Next ==
    \* The next state is the sequence obtained by adding the next element to the current sequence.
    \/ \E s \in ZSeq(Jug) : s' = [s \cup {Jug}]

Inv ==
    \* The invariant is that the sequence is non-empty.
    \A s \in ZSeq(Jug) : s \neq <<>>

TypeOK ==
    \* The type invariant.
    /\ Goal \in Nat
    /\ Jug \in {1, 2, 3}
    /\ Capacity \in {1, 2, 3}
    /\ [s \in ZSeq(Jug) |-> ZLen(s)] \in Nat
    /\ [s \in ZSeq(Jug) |-> ZLen(s)] \subseteq Nat

NotSolved ==
    \* The property that the sequence is not solved.
    \/ \E s \in ZSeq(Jug) : ZLen(s) < Goal

Spec == Init /\ [][Next]_<<s>> /\ Inv /\ [](TypeOK /\ NotSolved)

=============================================================================
====