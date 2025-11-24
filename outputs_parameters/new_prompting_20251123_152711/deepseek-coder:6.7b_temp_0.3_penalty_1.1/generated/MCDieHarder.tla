---- MODULE MCDieHarder ----
EXTENDS Module DieHarder

CONSTANTS MCJug = \* The set of all jugs
    {1, 2}

VARIABLES Jug <<MCJug>>

MCCapacity(j) ==
    CASE j OF
        1 -> 3
        2 -> 4
    ESAC

Spec ==
    /\ Init /\ []Next_<<Jug>>

TypeOK ==
    \E j \in Jug : Capacity[j] = 5

NotSolved ==
    ~([]GoalInFirstTwo)
====