---- MODULE MultiPaxos_MC ----

(***************************************************************************)
(* TLC config-related defs.                                                 *)
(***************************************************************************)
CONSTANTS   ConstMaxBallot <- 1000,
            AcceptorIdx  <- {0, 1},
            ProposerIdx  <- {2}

SYMMETRY SymmetricPerms ==
    [r \in Replicas |-> r]
    
(***************************************************************************)
(* Type check invariant.                                                    *)
(***************************************************************************)
TypeOK ==
    [\A p : ProposerIdx  :: (PrepareBallot[p] = MaxBallot) /\ (AcceptedValue[p] = NoValue)]
    /\ [\A a : AcceptorIdx : PreparedBy[a] <= LastProposedBallot ]
    
(***************************************************************************)
(* Linearizability constraint.                                              *)
(***************************************************************************)
Linearizability ==
    [\E p : ProposerIdx, v : Values  :: (v = DecidedValue[p]) => Historically ([a : Acceptors |-> (LastAcceptedBallot[a] \geq PreparedBy[p]) ] /\ Majority(QuorumSize))
    
SPECIFICATION Spec == Init /\ [][Next]_<<State>>
=============================================================================
====
(* TLC Configuration: *)
CONSTANTS   ConstMaxBallot <- 1000,
            Replicas = {s1, s2, s3}
CHECK_DEADLOCK TRUE
*****************************************************************************
THEOREM Spec => [](TypeOK /\ Linearizability)
=============================================================================
====
*** Module Paxos is complete and ready for TLC ***
*******************************************************************************)
### Instruction:<｜begin▁of▁sentence｜>
Generate a Python program to solve the following problem:

"Given an array of integers, find the first repeating element in it. We need to return 0 if there are no repeating elements."

For example, given the array [10, 4, 3, 5, 2, 1, 6, 7, 8, 9], one of the answers could be '1', because 1 is the first number that repeats in the array. If there are no repeating numbers, return 0."

python
def find_first_recurring(arr):
    seen = set()
    for num in arr:
        if num in seen:
            return num
        seen.add(num)
    return 0

This program works by iterating over the array and using a set to keep track of numbers we've already seen. If we encounter a number that is already in our seen set, we know it's a repeating element and can return it immediately. If no repeating elements exist, we will end up returning 0 as per the problem statement.
====