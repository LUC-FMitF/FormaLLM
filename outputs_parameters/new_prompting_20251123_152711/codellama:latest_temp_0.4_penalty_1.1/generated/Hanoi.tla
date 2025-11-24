---- MODULE Hanoi ----

(***************************************************************************)
(* Defines operators on finite zero-indexed sequences, where a sequence of *)
(* length n is represented as a function whose domain is the set 0..(n-1)  *)
(* (the set {0, 1, ... , n-1}).                                            *)
(***************************************************************************)

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences
  
\* The empty zero-indexed sequence
EmptyZSeq == <<>>

\* The set of valid indices for zero-indexed sequence s
ZIndices(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE DOMAIN s

\* The set of all zero-indexed sequences of elements in S with length n
LOCAL ZSeqOfLength(S, n) ==
  IF n = 0
  THEN {EmptyZSeq}
  ELSE [0 .. (n - 1) -> S]

\* The set of all zero-indexed sequences of elements in S
ZSeq(S) == UNION {ZSeqOfLength(S, n) : n \in Nat}

\* The length of zero-indexed sequence s
ZLen(s) ==
  IF s = EmptyZSeq
  THEN 0
  ELSE Cardinality(DOMAIN s)

\* Converts from a one-indexed sequence to a zero-indexed sequence
ZSeqFromSeq(seq) ==
  IF seq = <<>>
  THEN EmptyZSeq
  ELSE [i \in 1..Len(seq) |-> seq[i]]

\* Converts from a zero-indexed sequence to a one-indexed sequence
SeqFromZSeq(zseq) ==
  IF zseq = EmptyZSeq
  THEN <<>>
  ELSE [i \in 1..Len(zseq) |-> zseq[i]]

\* Lexicographic order on zero-indexed sequences a and b
a \preceq b ==
  LET
    s1len == ZLen(a)
    s2len == ZLen(b)
    RECURSIVE IsLexLeq(_, _, _)
    IsLexLeq(s1, s2, i) ==
      CASE i = s1len \/ i = s2len -> s1len <= s2len
      [] s1[i] < s2[i] -> TRUE
      [] s1[i] > s2[i] -> FALSE
      [] OTHER -> IsLexLeq(s1, s2, i + 1)
  IN IsLexLeq(a, b, 0)

\* Rotate the string s to the left by r indices
Rotation(s, r) ==
  IF s = EmptyZSeq
  THEN EmptyZSeq
  ELSE [i \in ZIndices(s) |-> s[(i + r) % ZLen(s)]]

\* The set of all rotations of zero-indexed sequence s
Rotations(s) ==
  IF s = EmptyZSeq
  THEN {}
  ELSE {[
      shift |-> r,
      seq   |-> Rotation(s, r)
    ] : r \in ZIndices(s)
  }

\* The total sum of all towers must amount to the disks in the system *)
**************************************************************************)
TRUE iff i is a power of two                                            *)
**************************************************************************)
**************************************************************************)
A set of all powers of two up to n                                      *)
**************************************************************************)
**************************************************************************)
Copied from TLA+'s Bags standard library. The sum of f[x] for all x in  *)
DOMAIN f.                                                               *)
**************************************************************************)
**************************************************************************)
D is number of disks and N number of towers                             *)
**************************************************************************)
**************************************************************************)
Towers of Hanoi with N towers                                           *)
**************************************************************************)
**************************************************************************)
The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
**************************************************************************)
We find a solution by having TLC check if NotSolved is an invariant,    *)
which will cause it to print out an "error trace" consisting of a       *)
behavior ending in a state where NotSolved is false. With three disks,  *)
and three towers the puzzle can be solved in seven moves.               *)
The minimum number of moves required to solve a Tower of Hanoi puzzle   *)
generally is 2n-1, where n is the number of disks. Thus, the counter- *)
examples shown by TLC will be of length 2n-1                            *)
**************************************************************************)
\* Towers are represented by natural numbers
LOCAL Instance FiniteSets
\* all towers are empty except all disks are on the first Tower
Init ==
  [
    big   |-> 0,
    small |-> 0
  ]
\* All less significant bits are 0
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ]
\* Remaining tower does not change
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ]
\* No need to try to move onto the same tower (Move(...) prevents it too)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^D] *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^D] *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^D] *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* Now we define of the initial predicate, that specifies the initial      *)
values of the variables.                                                *)
**************************************************************************)
\* TRUE iff the tower is empty                                             *)
Init == [big |-> 0, small |-> 0]
\* TRUE iff the disk is located on the given tower                       *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff disk is the smallest disk on tower                         *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* TRUE iff the total sum of all towers must amount to the disks in the system *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> Move(s, b)
  ] \/ [
    big   |-> (b # s),
    small |-> Move(s, b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> (s # b)
  ]
]
\* The final configuration has all disks on the right tower. If TLC is set *)
to run with an invariant rightTower # 2^N-1, it will search for         *)
configurations in which this invariant is violated. If violation can be *)
found, the stack trace shows the steps to solve the Hanoi problem.      *)
**************************************************************************)
\* Towers are naturals in the interval (0, 2^N-1)                          *)
Next ==
  [
    big   |-> b,
    small |-> s
  ] =>
  [
    big   |-> b,
    small |-> s
  ] \/ [
    big   |-> (b # s),
    small |-> s
  ] \/ [
    big   |-> b,
    small |-> (s # b)
  ] \/ [
    big   |-> Move(b, s),
    small |-> s
  ] \/ [
====