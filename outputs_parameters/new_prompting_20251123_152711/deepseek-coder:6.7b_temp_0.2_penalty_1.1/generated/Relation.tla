---- MODULE Relation ----
TransClosure == [x, y \in S | (x, y) \in R OR (\A u \in S: (u, x) \in R /\ (x, y) \in R)]
====