---------------------------- MODULE product ----------------------------

EXTENDS Naturals, Sequences

CONSTANTS DNA, PRIMER

VARIABLES tee,
stage,
cycle,
primer,

longTemplate,
shortTemplate,
tinyTemplate,

longHybrid,
shortHybrid,
tinyHybrid,

longLongDouble,
shortLongDouble,
tinyShortDouble,

product

vars == <<tee,
stage,
cycle,
primer,

longTemplate,
shortTemplate,
tinyTemplate,

longHybrid,
shortHybrid,
tinyHybrid,

longLongDouble,
shortLongDouble,
tinyShortDouble,

product
>>

templates == <<longTemplate,
shortTemplate,
tinyTemplate>>

hybrids == <<longHybrid,
shortHybrid,
tinyHybrid>>

doubles == <<longLongDouble,
shortLongDouble,
tinyShortDouble,
product>>

natMin(i,j) == IF i < j THEN i ELSE j
RECURSIVE sumList(_)
sumList(s) == IF s = <<>> THEN 0 ELSE Head(s) + sumList(Tail(s))

heat ==    /\ tee = "Hot"
/\ tee' = "TooHot"
/\ primer' = primer + sumList(hybrids)

/\ longLongDouble' = 0
/\ shortLongDouble' = 0
/\ tinyShortDouble' = 0
/\ product' = 0

/\ longHybrid' = 0
/\ shortHybrid' = 0
/\ tinyHybrid' = 0

/\ longTemplate' = longTemplate + longHybrid + shortLongDouble + 2 * longLongDouble
/\ shortTemplate' = shortTemplate + shortHybrid + shortLongDouble + tinyShortDouble
/\ tinyTemplate' = tinyTemplate + tinyHybrid + tinyShortDouble + 2 * product

/\ (stage = "init" \/ stage = "extended")
/\ stage' = "denatured"
/\ UNCHANGED cycle

cool ==   /\ tee = "TooHot"
/\ tee' = "Hot"
/\ stage = "denatured"
/\ stage' = "ready"
/\ UNCHANGED <<cycle, primer>>
/\ UNCHANGED doubles
/\ UNCHANGED templates
/\ UNCHANGED hybrids

anneal ==   /\ tee = "Hot"
/\ tee' = "Warm"

/\ \E k \in 1..natMin(primer, sumList(templates)) :
/\ primer' = primer - k

/\ \E tup \in ((0..longTemplate) \X (0..shortTemplate) \X (0..tinyTemplate)):
/\ sumList(tup) = k
/\ longTemplate' = longTemplate - tup[1]
/\ longHybrid' = longHybrid + tup[1]
/\ shortTemplate' = shortTemplate - tup[2]
/\ shortHybrid' = shortHybrid + tup[2]
/\ tinyTemplate' = tinyTemplate - tup[3]
/\ tinyHybrid' = tinyHybrid + tup[3]
/\ stage = "ready"
/\ stage' = "annealed"
/\ UNCHANGED cycle
/\ UNCHANGED doubles

extend ==   /\ tee = "Warm"
/\ tee' = "Hot"

/\ UNCHANGED primer
/\ UNCHANGED templates

/\ UNCHANGED longLongDouble
/\ shortLongDouble' = shortLongDouble + longHybrid
/\ tinyShortDouble' = tinyShortDouble + shortHybrid
/\ product' = product + tinyHybrid

/\ longHybrid' = 0
/\ shortHybrid' = 0
/\ tinyHybrid' = 0

/\ stage = "annealed"
/\ stage' = "extended"
/\ cycle' = cycle + 1

Init == /\ tee = "Hot"
/\ primer = PRIMER
/\ longLongDouble = DNA

/\ longTemplate = 0
/\  shortTemplate = 0
/\  tinyTemplate = 0

/\  longHybrid = 0
/\  shortHybrid = 0
/\  tinyHybrid = 0

/\  shortLongDouble = 0
/\  tinyShortDouble = 0
/\  product = 0

/\ stage = "init"
/\ cycle = 0

Next == \/ heat
\/ cool
\/ anneal
\/ extend

Spec == /\ Init
/\ [][Next]_vars
/\ WF_vars(anneal)
/\ WF_vars(heat)
/\ WF_vars(cool)
/\ WF_vars(extend)

TypeOK ==
/\ tee \in {"Warm", "Hot", "TooHot"}
/\ primer \in Nat
/\ stage \in {"init","ready","annealed","extended","denatured"}
/\ cycle \in Nat
/\ longTemplate \in Nat
/\ shortTemplate \in Nat
/\ tinyTemplate \in Nat
/\ longHybrid \in Nat
/\ shortHybrid \in Nat
/\ tinyHybrid \in Nat
/\ longLongDouble \in Nat
/\ shortLongDouble \in Nat
/\ tinyShortDouble \in Nat
/\ product \in Nat

thirdCycleProduct == ((cycle < 3) => (product = 0))

stagesInstance == INSTANCE stages WITH
template <- sumList(templates),
hybrid <- sumList(hybrids),
dna <- sumList(doubles)

stagesSpec == stagesInstance!Spec

primerDepleted == stagesInstance!primerDepleted

=============================================================================
