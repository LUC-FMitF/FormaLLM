---- MODULE DiningPhilosophers ----

EXTENDS Integers, TLC

CONSTANTS

NP

ASSUME
/\ NP \in Nat \ {0}

VARIABLES forks, pc

LeftFork(p) == p
RightFork(p) == IF p = NP THEN 1 ELSE p + 1

LeftPhilosopher(p) == IF p = 1 THEN NP ELSE p - 1
RightPhilosopher(p) == IF p = NP THEN 1 ELSE p + 1

IsHoldingBothForks(p) ==
forks[LeftFork(p)].holder = p /\ forks[RightFork(p)].holder = p
BothForksAreClean(p) ==
forks[LeftFork(p)].clean /\ forks[RightFork(p)].clean

CanEat(p) == IsHoldingBothForks(p) /\ BothForksAreClean(p)

VARIABLE hungry

vars == << forks, pc, hungry >>

ProcSet == (1..NP)

Init ==
/\ forks =         [
fork \in 1..NP |-> [

holder |-> IF fork = 2 THEN 1 ELSE fork,

clean |-> FALSE
]
]

/\ hungry = [self \in 1..NP |-> TRUE]
/\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
/\ IF /\ forks[LeftFork(self)].holder = self
/\ ~forks[LeftFork(self)].clean
THEN /\ forks' = [forks EXCEPT ![LeftFork(self)] =                          [
holder |-> LeftPhilosopher(self),
clean |-> TRUE
]]
ELSE /\ IF /\ forks[RightFork(self)].holder = self
/\ ~forks[RightFork(self)].clean
THEN /\ forks' = [forks EXCEPT ![RightFork(self)] =                           [
holder |-> RightPhilosopher(self),
clean |-> TRUE
]]
ELSE /\ TRUE
/\ forks' = forks
/\ IF hungry[self]
THEN /\ IF CanEat(self)
THEN /\ pc' = [pc EXCEPT ![self] = "Eat"]
ELSE /\ pc' = [pc EXCEPT ![self] = "Loop"]
ELSE /\ pc' = [pc EXCEPT ![self] = "Think"]
/\ UNCHANGED hungry

Think(self) == /\ pc[self] = "Think"
/\ hungry' = [hungry EXCEPT ![self] = TRUE]
/\ pc' = [pc EXCEPT ![self] = "Loop"]
/\ forks' = forks

Eat(self) == /\ pc[self] = "Eat"
/\ hungry' = [hungry EXCEPT ![self] = FALSE]
/\ forks' = [forks EXCEPT ![LeftFork(self)].clean = FALSE,
![RightFork(self)].clean = FALSE]
/\ pc' = [pc EXCEPT ![self] = "Loop"]

Philosopher(self) == Loop(self) \/ Think(self) \/ Eat(self)

Next == (\E self \in 1..NP: Philosopher(self))

Spec == /\ Init /\ [][Next]_vars
/\ \A self \in 1..NP : WF_vars(Philosopher(self))

----

----

ShareFork(p, q) ==
{LeftFork(p), RightFork(p)} \cap {LeftFork(q), RightFork(q)} /= {}

----

----

TypeOK ==
/\ forks \in [1..NP -> [holder: 1..NP, clean: BOOLEAN]]
/\ hungry \in [1..NP -> BOOLEAN]
/\ pc \in [1..NP -> {"Loop", "Eat", "Think"}]

ExclusiveAccess ==
\A p,q \in 1..NP:
p /= q /\ ShareFork(p, q) => ~(pc[p] = "Eat" /\ pc[q] = "Eat")

----

----

NobodyStarves == \A p \in 1..NP: []<>(~hungry[p])

====
