---- MODULE Hanoi ----

(***************************************************************************)
(* Towers of Hanoi.                                                        *)
(***************************************************************************)

CONSTANTS
  D, N : Nat

VARIABLES
  big, small : Nat

CONSTANTS
  One, Two, Three : Nat

Init ==
  D = 3 /\ N = 3 /\
  big = 2^3 - 1 /\ small = 0

Next ==
  CASE
    [big' = big, small' = small] ->
      (ONE_OVER_TowersOfHanoi(big, small) \/
       ONE_UNDER_TowersOfHanoi(big, small) \/
       BOTH_OVER_TowersOfHanoi(big, small) \/
       BOTH_UNDER_TowersOfHanoi(big, small))
    [big' = big, small' = small'] ->
      (ONE_OVER_TowersOfHanoi(big, small) \/
       ONE_UNDER_TowersOfHanoi(big, small) \/
       BOTH_OVER_TowersOfHanoi(big, small) \/
       BOTH_UNDER_TowersOfHanoi(big, small))
  :
    ONE_OVER_TowersOfHanoi(big, small) \/
    ONE_UNDER_TowersOfHanoi(big, small) \/
    BOTH_OVER_TowersOfHanoi(big, small) \/
    BOTH_UNDER_TowersOfHanoi(big, small)

ONE_OVER_TowersOfHanoi(b, s) ==
  b = 2^N - 1 /\ s = 0

ONE_UNDER_TowersOfHanoi(b, s) ==
  b = 0 /\ s = 2^N - 1

BOTH_OVER_TowersOfHanoi(b, s) ==
  b = 2^N - 1 /\ s = 2^N - 1

BOTH_UNDER_TowersOfHanoi(b, s) ==
  b = 0 /\ s = 0

Spec ==
  Init /\ [big', small'] \in Next /\ big' = small'

NotSolved ==
  big = small

=============================================================================
====