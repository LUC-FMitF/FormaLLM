---- MODULE BinarySearch ----

CONSTANTS Values, SortedSeqs

VARIABLES seq \in SortedSeqs, val \in Values,
          low = 1, high = Len(seq), result = 0;

Init ==
  /\ seq \in SortedSeqs
  /\ val \in Values
  /\ low = 1
  /\ high = Len(seq)
  /\ result = 0;

NextState ==
  [ low = low + 1, high = mid - 1 ] \/
  [ low = mid + 1, high = high ] \/
  [ result = mid ]
  where mid = (low + high) \div 2, mval = seq[mid];

Inv == low <= high /\ (result = 0 \/ result = mid);

Spec == Init /\ [](Inv)

=============================================================================
====