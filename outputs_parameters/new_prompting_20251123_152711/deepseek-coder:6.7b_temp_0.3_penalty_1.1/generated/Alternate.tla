---- MODULE Alternate ----
INVARIANTS TypeOK == \E x : XInitValue /\ (v = 0 -> x = XInitValue)
====