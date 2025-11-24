---- MODULE BufferedRandomAccessFile ----
(***************************************************************************)
(* Copyright (c) 2024, Oracle and/or its affiliates.                         *)
(* This is a model-checkable specification for BufferedRandomAccessFile.java. *)
(* It covers the core fields as well as the seek, read, write, flush, and       *)
(* setLength operations.                                                      *)
(***************************************************************************)

EXTENDS ModuleName

CONSTANTS 
  Symbols = {A, B}
  ArbitrarySymbol = ArbitrarySymbol
  MaxOffset = 3
  BuffSz = 2
  
\* Variables and Invariants defined in .java file
LOCAL VARIABLE c(f)
LOCAL VARIABLE disk(f)[i]
LOCAL INVARIANT Inv1 = \* ...
LOCAL INVARIANT Inv2 = \* ...
LOCAL INVARIANT Inv3 = \* ...
LOCAL INVARIANT Inv4 = \* ...
LOCAL INVARIANT Inv5 = \* ...
  
\* Operations defined in .java file
OPERATION Seek(pos) 
OPERATION FlushBuffer()
OPERATION WriteAtMost(data, pos)
OPERATION Read(numBytes, pos)
OPERATION SetLength(newLen)
  
\* Properties defined in .java file
PROPERTY Inv2CanAlwaysBeRestored = \* ...
PROPERTY Safety = \* ...
PROPERTY FlushBufferCorrect = \* ...
PROPERTY SeekCorrect = \* ...
PROPERTY SeekEstablishesInv2 = \* ...
PROPERTY Write1Correct = \* ...
PROPERTY Read1Correct = \* ...
PROPERTY WriteAtMostCorrect = \* ...
PROPERTY ReadCorrect = \* ...
  
=============================================================================
====
TLC Configuration:
SPECIFICATION Spec
CONSTANT Symbols = {A, B}
CONSTANT ArbitrarySymbol = ArbitrarySymbol
CONSTANT MaxOffset = 3
CONSTANT BuffSz = 2

SYMMETRY Symmetry
ALIAS Alias

INVARIANT TypeOK
INVARIANT Inv1
INVARIANT Inv2
PROPERTY Inv2CanAlwaysBeRestored
INVARIANT Inv3
INVARIANT Inv4
INVARIANT Inv5
PROPERTY Safety
PROPERTY FlushBufferCorrect
PROPERTY SeekCorrect
PROPERTY SeekEstablishesInv2
PROPERTY Write1Correct
PROPERTY Read1Correct
PROPERTY WriteAtMostCorrect
PROPERTY ReadCorrect
====