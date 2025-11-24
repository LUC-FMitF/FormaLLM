---- MODULE Hanoi ----
Module Hanoi

  (* Define the number of towers and disks *)
  const N = 3;
  const D = 3;

  (* Initialize the towers with all disks on the first tower *)
  Init == towers = {Pow(2, D)} /\ disks = Pow(2, D)

  (* Next predicate *)
  Next(x) == x \in {Move(d, from, to) : d \in disks, from \in towers, to \in towers /\ from \neq to}

  (* Specification *)
  Spec == <<towers, disks>> \in Init /\ TotalSize(towers) = D /\ rightTower # 2^N - 1 /\ NotSolved /\
         (FORALL d \in disks, EXISTS from \in towers, to \in towers /\ Move(d, from, to))

  (* Invariant: rightTower *)
  rightTower == LET rightmost == MaxElement(towers) IN Cardinality(towers) = D /\ rightmost = MaxElement(towers)

  (* NotSolved invariant *)
  NotSolved == LET rightmost == MaxElement(towers) IN rightmost = 2^D - 1

  (* Counter-examples are of length 2n-1, where n is the number of disks *)
  CounterExampleLength == 2 * D - 1

endmodule
====