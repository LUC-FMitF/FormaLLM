------------------------------- MODULE TLCMC -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

SetToSeqs(set, Filter(_)) == UNION {{perm \in [1..Cardinality(set) -> set]:

Filter(perm)}}

SetToDistSeqs(set) == SetToSeqs(set,
LAMBDA p: Cardinality(SeqToSet(p)) = Cardinality(set))

IsGraph(G) == /\ {"states", "initials", "actions"} = DOMAIN G
/\ G.actions \in [G.states -> SUBSET G.states]
/\ G.initials \subseteq G.states

SetOfAllPermutationsOfInitials(G) == SetToDistSeqs(G.initials)

SuccessorsOf(state, SG) == {successor \in SG.actions[state]:
successor \notin {state}}

Predecessor(t, v) == SelectSeq(t, LAMBDA pair: pair[2] = v)[1][1]

CONSTANT StateGraph, ViolationStates, null

ASSUME
\/ IsGraph(StateGraph)

\/ ViolationStates \subseteq StateGraph.states

init: while (i \leq Len(S)) {

state := S[i];

C := C \cup {state};
i := i + 1;
if (state \in ViolationStates) {
counterexample := <<state>>;

goto trc;
};
};

initPost: assert C = SeqToSet(S);

scsr: while (Len(S) # 0) {

state := Head(S);

S := Tail(S);

successors := SuccessorsOf(state, StateGraph) \ C;
if (SuccessorsOf(state, StateGraph) = {}) {

counterexample := <<state>>;
goto trc;
};
each: while (successors # {}) {
with (succ \in successors) {

successors := successors \ {succ};

C := C \cup {succ}; S := S \o <<succ>>;

T  := T \o << <<state,succ>> >>;

if (succ \in ViolationStates) {
counterexample := <<succ>>;

goto trc;
};
};
};
};

assert S = <<>> /\ ViolationStates = {};
goto Done;

trc : while (TRUE) {
if (Head(counterexample) \notin StateGraph.initials) {
counterexample := <<Predecessor(T, Head(counterexample))>> \o counterexample;
} else {
assert counterexample # <<>>;
goto Done;
};
};
}
}
***************************************************************************)

VARIABLES S, C, state, successors, i, counterexample, T, pc

vars == << S, C, state, successors, i, counterexample, T, pc >>

Init ==
/\ S \in SetOfAllPermutationsOfInitials(StateGraph)
/\ C = {}
/\ state = null
/\ successors = {}
/\ i = 1
/\ counterexample = <<>>
/\ T = <<>>
/\ pc = "init"

init == /\ pc = "init"
/\ IF i \leq Len(S)
THEN /\ state' = S[i]
/\ C' = (C \cup {state'})
/\ i' = i + 1
/\ IF state' \in ViolationStates
THEN /\ counterexample' = <<state'>>
/\ pc' = "trc"
ELSE /\ pc' = "init"
/\ UNCHANGED counterexample
ELSE /\ pc' = "initPost"
/\ UNCHANGED << C, state, i, counterexample >>
/\ UNCHANGED << S, successors, T >>

initPost == /\ pc = "initPost"
/\ Assert(C = SeqToSet(S),
"Failure of assertion at line 116, column 18.")
/\ pc' = "scsr"
/\ UNCHANGED << S, C, state, successors, i, counterexample, T >>

scsr == /\ pc = "scsr"
/\ IF Len(S) # 0
THEN /\ state' = Head(S)
/\ S' = Tail(S)
/\ successors' = SuccessorsOf(state', StateGraph) \ C
/\ IF SuccessorsOf(state', StateGraph) = {}
THEN /\ counterexample' = <<state'>>
/\ pc' = "trc"
ELSE /\ pc' = "each"
/\ UNCHANGED counterexample
ELSE /\ Assert(S = <<>> /\ ViolationStates = {},
"Failure of assertion at line 164, column 8.")
/\ pc' = "Done"
/\ UNCHANGED << S, state, successors, counterexample >>
/\ UNCHANGED << C, i, T >>

each == /\ pc = "each"
/\ IF successors # {}
THEN /\ \E succ \in successors:
/\ successors' = successors \ {succ}
/\ C' = (C \cup {succ})
/\ S' = S \o <<succ>>
/\ T' = T \o << <<state,succ>> >>
/\ IF succ \in ViolationStates
THEN /\ counterexample' = <<succ>>
/\ pc' = "trc"
ELSE /\ pc' = "each"
/\ UNCHANGED counterexample
ELSE /\ pc' = "scsr"
/\ UNCHANGED << S, C, successors, counterexample, T >>
/\ UNCHANGED << state, i >>

trc == /\ pc = "trc"
/\ IF Head(counterexample) \notin StateGraph.initials
THEN /\ counterexample' = <<Predecessor(T, Head(counterexample))>> \o counterexample
/\ pc' = "trc"
ELSE /\ Assert(counterexample # <<>>,
"Failure of assertion at line 177, column 20.")
/\ pc' = "Done"
/\ UNCHANGED counterexample
/\ UNCHANGED << S, C, state, successors, i, T >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == init \/ initPost \/ scsr \/ each \/ trc
\/ Terminating

Spec == /\ Init /\ [][Next]_vars
/\ WF_vars(Next)

Termination == <>(pc = "Done")

Live == ViolationStates # {} => <>[](/\ Len(counterexample) > 0
/\ counterexample[Len(counterexample)] \in ViolationStates
/\ counterexample[1] \in StateGraph.initials)

=============================================================================
