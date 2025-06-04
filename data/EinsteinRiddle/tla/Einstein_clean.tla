------------------- MODULE Einstein ------------------------

EXTENDS Naturals, FiniteSets, Apalache

House == 1..5

Permutation(S) == {
FunAsSeq(p, 5, 5) : p \in {
p \in [ House -> S ] :
/\ p[2] \in S \ {p[1]}
/\ p[3] \in S \ {p[1], p[2]}
/\ p[4] \in S \ {p[1], p[2], p[3]}
/\ p[5] \in S \ {p[1], p[2], p[3], p[4]}
}
}

NATIONALITIES == Permutation({ "brit", "swede", "dane", "norwegian", "german" })
DRINKS == Permutation({ "beer", "coffee", "mylk", "tea", "water" })
COLORS == Permutation({ "red", "white", "blue", "green", "yellow" })
PETS == Permutation({ "bird", "cat", "dog", "fish", "horse" })
CIGARS == Permutation({ "blend", "bm", "dh", "pm", "prince" })

VARIABLES

nationality,

colors,

pets,

cigars,

drinks

------------------------------------------------------------

BritLivesInTheRedHouse == \E i \in 2..5 : nationality[i] = "brit" /\ colors[i] = "red"

SwedeKeepsDogs == \E i \in 2..5 : nationality[i] = "swede" /\ pets[i] = "dog"

DaneDrinksTea == \E i \in 2..5 : nationality[i] = "dane" /\ drinks[i] = "tea"

GreenLeftOfWhite == \E i \in 1..4 : colors[i] = "green" /\ colors[i + 1] = "white"

GreenOwnerDrinksCoffee == \E i \in 1..5 \ {3} : colors[i] = "green" /\ drinks[i] = "coffee"

SmokesPallmallRearsBirds == \E i \in 1..5 : cigars[i] = "pm" /\ pets[i] = "bird"

YellowOwnerSmokesDunhill == \E i \in 1..5 : colors[i] = "yellow" /\ cigars[i] = "dh"

CenterDrinksMylk == drinks[3] = "mylk"

NorwegianFirstHouse == nationality[1] = "norwegian"

BlendSmokerLivesNextToCatOwner ==
\E i \in 1..4 :
\/ cigars[i] = "blend" /\ pets[i + 1] = "cat"
\/ pets[i] = "cat" /\ cigars[i + 1] = "blend"

HorseKeeperLivesNextToDunhillSmoker ==
\E i \in 1..4 :
\/ cigars[i] = "dh" /\ pets[i + 1] = "horse"
\/ pets[i] = "horse" /\ cigars[i + 1] = "dh"

BluemasterSmokerDrinksBeer == \E i \in 1..5 : cigars[i] = "bm" /\ drinks[i] = "beer"

GermanSmokesPrince == \E i \in 2..5 : nationality[i] = "german" /\ cigars[i] = "prince"

NorwegianLivesNextToBlueHouse == colors[2] = "blue"

BlendSmokerHasWaterDrinkingNeighbor ==
\E i \in 1..4 :
\/ cigars[i] = "blend" /\ drinks[i + 1] = "water"
\/ drinks[i] = "water" /\ cigars[i + 1] = "blend"

------------------------------------------------------------

Init ==
/\ drinks \in { p \in DRINKS : p[3] = "mylk" }
/\ nationality \in { p \in NATIONALITIES : p[1] = "norwegian" }
/\ colors \in { p \in COLORS : p[2] = "blue" }
/\ pets \in PETS
/\ cigars \in CIGARS

vars == <<nationality, colors, cigars, pets, drinks>>

Next ==
UNCHANGED vars

Spec == Init /\ [][Next]_vars

Solution ==
/\ BritLivesInTheRedHouse
/\ SwedeKeepsDogs
/\ DaneDrinksTea
/\ GreenLeftOfWhite
/\ GreenOwnerDrinksCoffee
/\ SmokesPallmallRearsBirds
/\ YellowOwnerSmokesDunhill
/\ CenterDrinksMylk
/\ NorwegianFirstHouse
/\ BlendSmokerLivesNextToCatOwner
/\ HorseKeeperLivesNextToDunhillSmoker
/\ BluemasterSmokerDrinksBeer
/\ GermanSmokesPrince
/\ NorwegianLivesNextToBlueHouse
/\ BlendSmokerHasWaterDrinkingNeighbor

FindSolution == ~Solution

============================================================
