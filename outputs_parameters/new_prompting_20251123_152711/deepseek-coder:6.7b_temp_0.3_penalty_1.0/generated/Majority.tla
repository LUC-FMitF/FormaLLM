---- MODULE Majority 
EXTENDS FiniteSets, Naturals, Sequences, ZSequences

CONSTANTS 
  EmptySeq == <<>>

VARIABLES 
  seq, next, cand, lb, prefix, count, total == EmptySeq

ASSUME 
  \* input sequence of values, never changes
  INIT == seq' = seq

  \* next position of sequence to be checked
  next' == IF next = EmptySeq THEN seq ELSE next + 1

  \* current candidate for having a majority
  cand' == IF lb > 1/2 * Cardinality(seq) THEN cand ELSE nextValue(cand)

  \* lower bound for the number of occurrences of the candidate so far
  lb' == IF nextValue(cand) = cand THEN lb ELSE IF seq[next] = cand THEN lb + 1 ELSE lb

  \* set of indexes in the prefix of the sequence strictly before j holding v
  prefix' == IF seq[next] = cand THEN Append(prefix, next) ELSE prefix

  \* number of times v occurs in that prefix
  count' == IF seq[next] = cand THEN count + 1 ELSE count

  \* number of times v occurs in all of the sequence
  total' == IF seq[next] = cand THEN total + 1 ELSE total

INVARIANTS 
  \* main correctness property: cand can be the only value that has a majority
  Inv == cand = NextValue(cand) -> lb > 1/2 * Cardinality(seq)

  \* inductive invariant for proving correctness
  Inv' == Inv /\ (seq[next] = cand -> lb' > 1/2 * Cardinality(seq))

SPECIFICATION 
  \* specification of the algorithm
  Spec == Inv /\ Inv'

TLC Configuration:
CONSTANTS
  MaxLen == 10

SPECIFICATION
  Spec /\ (seq = EmptySeq \/ Cardinality(seq) <= MaxLen)

====