---- MODULE BufferedRandomAccessFile ----
(***************************************************************************)
(* Copyright (c) 2024, Oracle and/or its affiliates.                        *)
(* This is a model-checkable specification for BufferedRandomAccessFile.java. *)
(* It covers the core fields as well as the seek, read, write, flush, and     *)
(* setLength operations.                                                     *)
(***************************************************************************)

EXTENDS ModuleName

CONSTANTS 
    Symbols = {A, B}
    ArbitrarySymbol = ArbitrarySymbol
    MaxOffset = 3
    BuffSz = 2

VARIABLES
    f /\ File
    lo /\ Natural
    file_pointer /\ Natural
    buff /\ [0 .. (BuffSz - 1)] -> Symbols
    dirty /\ Boolean
    Inv2 /\ Boolean

ASSUMPTIONS
    (* Assumptions about the underlying file f *)

DEFINITIONS
    ZeroIndexedArray(a) == [i \in 0..<Len(a) |-> a[i]]

OPERATIONS
    InitializeFile() ==
        (* Initialization code here *)

    Seek(pos) ==
        (* Seek operation implementation here *)

    SetLength(len) ==
        (* SetLength operation implementation here *)

    Read(n) ==
        (* Read operation implementation here *)

    Write(data) ==
        (* Write operation implementation here *)

    FlushBuffer() ==
        (* FlushBuffer operation implementation here *)

    restoreInvariantsAfterIncreasingCurr() ==
        (* Code to restore invariants after increasing curr *)

INVARIANTS 
    TypeOK,
    Inv1,
    (*Inv2*),
    Inv3,
    Inv4,
    Inv5

PROPERTIES
    Inv2CanAlwaysBeRestored,
    Safety,
    FlushBufferCorrect,
    SeekCorrect,
    SeekEstablishesInv2,
    Write1Correct,
    Read1Correct,
    WriteAtMostCorrect,
    ReadCorrect

SPECIFICATION Spec == InitializeFile() /\ (* Main specification here *)

====
CONSTANTS 
    Symbols = {A, B}
    ArbitrarySymbol = ArbitrarySymbol
    MaxOffset = 3
    BuffSz = 2

SYMMETRY Symmetry
ALIAS Alias

INVARIANTS TypeOK, Inv1, (*Inv2*), Inv3, Inv4, Inv5
PROPERTIES 
    Inv2CanAlwaysBeRestored, Safety, FlushBufferCorrect, SeekCorrect, 
    SeekEstablishesInv2, Write1Correct, Read1Correct, WriteAtMostCorrect, ReadCorrect
====