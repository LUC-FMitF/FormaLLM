---- MODULE BufferedRandomAccessFile ----
(***************************************************************************)
(* Copyright (c) 2024, Oracle and/or its affiliates.                       *)
(* This is a model-checkable specification for BufferedRandomAccessFile.java. *)
(* It covers the core fields as well as the seek, read, write, flush, and     *)
(* setLength operations.                                                     *)
(***************************************************************************)

EXTENDS ModuleName

CONSTANTS Symbols = {A, B}
CONSTANT ArbitrarySymbol = ArbitrarySymbol
CONSTANT MaxOffset = 3
CONSTANT BuffSz = 2

\* Symmetry: The symmetry relation is not specified in the comments. 
\* Alias: The alias relation is not specified in the comments. 

INVARIANTS TypeOK, Inv1, Inv2, Inv3, Inv4, Inv5
PROPERTIES Safety, FlushBufferCorrect, SeekCorrect, SeekEstablishesInv2, Write1Correct, Read1Correct, WriteAtMostCorrect, ReadCorrect
====