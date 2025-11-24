---- MODULE Hanoi ----
MODULE TowersOfHanoi

CONSTANTS D, N, Big, Small

VARIABLES Towers, Disk, Move

INITIAL 
  Towers ← [0..N-1]
  Disk ← Big

PREFUNCTION IsPowerOfTwo(i: Naturals)
  IF i ≠ 0 ∧ (i ∧ (i − 1)) ∧ (i ∧ (i − 2)) ∧ ... ∧ 2 ∧ 1 ∧ 0 ∧ ∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧∧
====