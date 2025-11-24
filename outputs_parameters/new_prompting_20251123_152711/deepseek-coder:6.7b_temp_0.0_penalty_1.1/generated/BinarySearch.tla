---- MODULE BinarySearch --------------------------------------
EXTENDS FiniteSets, Naturals, Sequences, ZSequences
CONSTANTS
   MaxLen = 3
VARIABLES
   seq \in Seq(Values), val \in Values, low, high, result, mid, mval
Init == (low = 1 /\ high = Len(seq) /\ result = 0)
Next == IF (low <= high /\ result = 0) THEN
            [mid = (low + high) DIV 2, mval = seq[mid]] /\
            IF (mval = val) THEN
              result := mid
            ELSE IF (val < mval) THEN
              high := mid - 1
            ELSE
              low := mid + 1
            ENDIF
          FI
        FI
      FI
Spec == Init /\ [][Next]_(low, high, result, mid, mval)

Inv(seq, val, low, high, result, mid, mval) ==
  IF (result = 0) THEN
    low <= high /\ seq[mid] = val OR high < low - 1
  ELSE
    result <= high /\ seq[result] = val
  FI

====