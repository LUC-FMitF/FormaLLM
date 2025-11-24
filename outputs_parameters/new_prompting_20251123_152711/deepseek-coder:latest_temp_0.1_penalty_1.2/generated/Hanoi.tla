---- MODULE Hanoi ----
MODULE TowersOfHanoi
(TRUE iff i is a power of two                                             *)
SPECIFICATION Spec                                                         *//* Define the specification */ 
INVARIANTS rightTower #2^N-1                                          /* Invariant: The final configuration has all disks on the right tower. If TLC is set to run with an invariant, it will search for configurations in which this invariant is violated and if violation can be found then stack trace shows steps */ 
INITIAL PREDICATES                                                      *//* Define initial predicates that specify the initial values of variables*/  
Init(i:Nat) == i = 2^D -1                                          /* Initial configuration has all disks on right tower and no disk is in a non-empty tower */ 
Next <<big, small>> unchanged                                        (* If Towers are empty except for All Disks Are On the First Tower then No need to try move onto same tower else Move(...) prevents it too)*/  
TRUE iff i is power of two                                          /* Define TRUE/iff rule that checks whether a number n (in this case, 'i') is a Power Of Two */ 
A set of all powers upto N                                              (* Defines the domain for function sumOfF which calculates Sum( f[x] ) over x in DOMAIN F.*/  
sumOfF == SUM {f:Nat} [ i DIVIDE (2^i) ]                          /* Define formula that sums all elements of set 'f' */ 
D, N = numberofdisks ,numberoftowers                               (* Defines the domain for function Towers and defines it as natural numbers up to n.*/  
Towers == {tower:Nat} [tower=2^(n-1)]                              /* Define formula that represents towers */ 
DiskOnTower <<disk, tower>> true                                     (* Defines the relation between disk on a particular tower and it is located in this specific position.*/  
CanMoveOff == {tower:Nat} [tower=2^(n-1)]                          /* Define formula that checks if Disk can be moved off of Tower */ 
CanMoveToTower <<disk, tower>> true                                  (* Defines the relation between disk and its destination for moving it to a specific position.*/  
SmallestDiskOnTop == {tower:Nat} [tower=2^(n-1)]                   /* Define formula that checks if Disk is smallest on top of Tower */ 
InitiallyEmptyExceptAllDisksAreFirstTower <<i, j>> true              (* Defines the relation between i and all towers except for one tower which has disks.*/  
END SPECIFICATION                                                       /* End specification definition */   
) ;                                                                     *//* Close module declaration  */
====