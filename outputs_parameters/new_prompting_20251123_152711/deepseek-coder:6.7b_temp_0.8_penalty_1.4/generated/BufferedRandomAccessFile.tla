---- MODULE BufferedRandomAccessFile ----
(*Copyright 2024, Oracle and/or its affiliates.
This is a model-checkable specification for BufferedRandomAccessFile.java.
It covers the core fields as well as the seek, read, write, flush, and setLength operations.*)

EXTENDS ModuleName (*Replace this with your general RandomAccessFile spec*)

CONSTANTS
  Symbols = {A, B} (*2 symbols: A and B*)
  ArbitrarySymbol = ArbitrarySymbol (*Arbitrary symbol to represent undefined bytes in the file*)
  MaxOffset = 3 (*Highest possible offset*)
  BuffSz = 2 (*Buffer size*)

(*Helper definitions for symmetry, alias and type-ok*)
SYMMETRY Symmetry == [](x: INT1) -> x
ALIAS Alias(f: FUNCTION INT1 -> BOOLEAN) == EXTENSION f := {[] x \in INT1 |-> f(x)} 
TypeOK == ELEMENTARY TYPES == {INT1, INT2} /\ SUBSET INT1 OF POSINT /\ SUBSET INT2 OF POSINT

INVARIANTS 
(* Internal invariants V1-V5 *)
Inv1 == [](x: INT1) -> x >= 0 /\ x <= MaxOffset (*Pointer is within legal range*)
Inv2 == [](x: INT1) -> c(f)[x] = disk(f)[x] (*Content at file pointer matches content on disk*)
(* Inv3-V5 are not defined in the original description *)

PROCEDURES 
(* Properties to be proved correctness *)
Inv2CanAlwaysBeRestored == [](x: INT1) -> Inv2(x) /\ Enable(FlushBuffer)(x) /\ ENABLED Seek(curr(f)) -> Inv2'(x')
Safety == [](x: INT1, x': INT1) -> (Inv1(x) /\ Inv2(x) /\ ~dirty(f) \/ FlushBuffer(x) = TRUE) -> Inv1(x') /\ Inv2(x')
FlushBufferCorrect == [](x: INT1, x': INT1) -> (Inv1(x) /\ ENABLED Seek(curr(f))) -> FlushBuffer(x) = TRUE /\ disk'(f) = disk(f)[x]
SeekCorrect == [](x: INT1, i: INT2, x': INT1) -> (Inv1(x) /\ ENABLED Inv2CanAlwaysBeRestored) -> Seek(i)(x) = TRUE /\ Inv1'(x') = i
SeekEstablishesInv2 == [](x: INT1, i: INT2, x': INT1) -> (Inv1(x) /\ ENABLED Inv2CanAlwaysBeRestored) -> Seek(i)(x) = TRUE -> Inv2'(x')
Write1Correct == [](x: INT1, a: ARRAY OF Symbols[0 .. BuffSz-1], x': INT1) -> (Inv1(x) /\ ENABLED Inv2CanAlreadyBeRestored) -> Write(a)(x) = TRUE
ReadCorrect == [](x: INT1, n: INT2, a: ARRAY OF Symbols[0 .. BuffSz-1], x': INT1) -> (Inv1(x) /\ ENABLED Inv2CanAlreadyBeRestored) -> Read(n)(x, a) = TRUE
WriteAtMostCorrect == [](x: INT1, n: INT2, a: ARRAY OF Symbols[0 .. BuffSz-1], x': INT1) -> (Inv1(x) /\ ENABLED Inv2CanAlreadyBeRestored) -> WriteAtMost(n)(a)(x) = TRUE
ReadCorrect == [](x: INT1, n: INT2, a: ARRAY OF Symbols[0 .. BuffSz-1], x': INT1) -> (Inv1(x) /\ ENABLED Inv2CanAlreadyBeRestored) -> Read(n)(x, a) = TRUE

(* Operations on the file *)
Seek == [](i: INT2, x: INT1) -> (*Helper for Seek*) (ENABLED FlushBuffer /\ ENABLED Inv2CanAlreadyBeRestored) -> Seek(i)(x) 
FlushBuffer == [](x: INT1) -> (*Sends the buffer to disk*) FlushBuffer(x)
WriteAtMost == [](n: INT2, a: ARRAY OF Symbols[0 .. BuffSz-1], x: INT1) -> (ENABLED Inv2CanAlreadyBeRestored /\ Inv1(x)) -> WriteAtMost(n)(a)(x)
Read == [](n: INT2, x: INT1, a: ARRAY OF Symbols[0 .. BuffSz-1]) -> (*Read data at the current position*) (ENABLED Inv2CanAlreadyBeRestored /\ Inv1(x)) -> Read(n)(x, a)
Write == [](a: ARRAY OF Symbols[0 .. BuffSz-1], x: INT1) -> (*Write data at the current position*) (ENABLED Inv2CanAlreadyBeRestored /\ Inv1(x)) -> Write(a)(x)

(* Operations on the file *)
SetLength == [](l: INT2, f: FUNCTION INT1 -> Symbols) -> (*Resize the data*) (ENABLED Inv2CanAlreadyBeRestored /\ Inv1(curr(f)) /\ l >= 0) -> SetLength(l)(f)
(* Contract of the file `write()` call *)
Write == [](a: ARRAY OF Symbols[0 .. BuffSz-1], x: INT1, f: FUNCTION INT1 -> Symbols) -> (ENABLED Inv2CanAlreadyBeRestored /\ Inv1(x)) -> Write(a)(f)(x)
(* Contract of the file `setLength()` call *)
SetLength == [](l: INT2, f: FUNCTION INT1 -<｜begin▁of▁sentence｜> Symbols[0 .. MaxOffset]) -> (*Truncate or extend with ArbitrarySymbol*) (ENABLED Inv2CanAlreadyBeRestored /\ l >= 0) -> SetLength(l)(f)
====