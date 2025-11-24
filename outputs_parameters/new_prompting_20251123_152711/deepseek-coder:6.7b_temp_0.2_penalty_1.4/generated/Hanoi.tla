---- MODULE Hanoi ----
(**************************************************************************)
(* Towers of Hanoi                                                        *)
(**************************************************************************)
CONSTANTS   N,             \* Number of towers.
            D              \* Number of disks.
VARIABLES   tower[N],       \* The state of each tower (empty or not).
            disk           \* All the disks in play.
----------------------------------------------------------------------------
PowerOfTwo(n) == EXISTS m : 2^m = n    (* True iff n is a power of two *)
PowersOfTwo <= {x : x IN NAT, PowerOfTwo(x)}   (* Set of all powers of two up to D *)
----------------------------------------------------------------------------
EmptyTower(t) == \E d : tower[d] = t    (* True iff the tower is empty *)
DiskOnTower(t, d) == EXISTS x : disk[x].top = (t, d)   (* True iff the disk is located on given tower *)
SmallestDisk(d) == ~EXISTS y : DiskOnTower((y.top).next, y)  (* True iff smallest disk in stacked onto a larger one *)
CanMoveOff(t, d) == EXISTS x : (x = d OR CanMoveOff(x)) AND SmallestDisk(d)   (* True iff can move off of tower *)
CanMoveTo(fromTower, toTower, diskSize) == ~EXISTS y : DiskOnTower((y.top).next, y)  (* True iff smallest stacked on top is larger than the one we want to put onto it *)
----------------------------------------------------------------------------
ACTION MoveOff(t: NAT): BOOLEAN = IF CanMoveOff(t) THEN (~EXISTS d : DiskOnTower((d.top).next, d)) ELSE FALSE FI   (* True iff disk can be moved off of tower *)
ACTION MoveTo(fromTower: NAT, toTower: NAT): BOOLEAN = IF CanMoveOff(toTower) AND DiskOnTower((Disk.top).next, (Disk.top)) THEN EXISTS d : Disk[d].size < fromTower ELSE FALSE FI   (* True iff disk can be moved to the tower *)
----------------------------------------------------------------------------
Init == \E t: NAT [tower[t] = Empty AND ~EXISTS x : DiskOnTower(x, (Disk.top).next)]  (* Initial predicate specifying initial values of variables *)
Next == ~EXISTS d : DiskOnTower((d.top).next, d) OR EXISTS t: NAT [CanMoveTo(t, ((t+1)\%N), disk[diskSize])]   (* Next state formula for Hanoi behavior *)
Spec == Init AND [\F [] big small = <<>> UNCHANGED BY Next]    (* Specification asserting initial values and every step satisfying next or unchanged by next *)
----------------------------------------------------------------------------
InvRightTower == ~EXISTS d : DiskOnTower((d.top).next, ((t+1)\%N))   (* Invariant checking if all disks are on the right tower (2^D - 1) *)
====