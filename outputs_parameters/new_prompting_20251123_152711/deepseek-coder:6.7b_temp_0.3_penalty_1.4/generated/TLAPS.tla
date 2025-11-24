---- MODULE TLAPS ----
/*******************************************************************************
Counter Model (Simple)
********************************************************************************/
MODULE COUNTER
VARIABLES
    count \in NONNEGATIVE_INTEGER := 0;
ASSIGNMENTS
    ==>count = IF count' = 1 THEN 0 ELSE count + 1 FI;
====