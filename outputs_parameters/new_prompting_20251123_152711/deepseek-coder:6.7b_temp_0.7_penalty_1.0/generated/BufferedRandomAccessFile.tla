---- MODULE BufferedRandomAccessFile ----
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT Symbols = {A, B}
CONSTANT ArbitrarySymbol = ArbitrarySymbol
CONSTANT MaxOffset = 3
CONSTANT BuffSz = 2

(* Definitions of operations *)
OPEN {
  open,
  close,
  seek,
  read,
  write,
  flush,
  setLength
}

(* Invariants *)
INVARIANT TypeOK
INVARIANT Inv1
(*INVARIANT Inv2*)
PROPERTY Inv2CanAlwaysBeRestored
INVARIANT Inv3
INVARIANT Inv4
INVARIANT Inv5

(* Properties *)
PROPERTY Safety
PROPERTY FlushBufferCorrect
PROPERTY SeekCorrect
PROPERTY SeekEstablishesInv2
PROPERTY Write1Correct
PROPERTY Read1Correct
PROPERTY WriteAtMostCorrect
PROPERTY ReadCorrect

(* Symmetry *)
Symmetry

(* Alias *)
ALIAS

(* TLC Configuration *)
SPECIFICATION Spec
CONSTANTS 
  Symbols = {A, B}
  ArbitrarySymbol = ArbitrarySymbol
  MaxOffset = 3
  BuffSz = 2

====