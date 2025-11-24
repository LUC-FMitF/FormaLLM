---- MODULE BufferedRandomAccessFile ----
(***************************************************************************)
(* Copyright 2024, Oracle and/or its affiliates.                            *)
(* This is a model-checkable specification for BufferedRandomAccessFile.java. *)
(* It covers the core fields as well as the seek, read, write, flush, and     *)
(* setLength operations.                                                     *)
(***************************************************************************)

EXTENDS Model

CONSTANTS 
    Symbols = {A, B}
    ArbitrarySymbol = ArbitrarySymbol
    MaxOffset = 3
    BuffSz = 2

VARIABLES 
    file_pointer, buff, lo, hi AS INTEGER
    dirty, closed AS BOOLEAN
    disk(i) IN Symbols FOR ALL i IN 0..MaxOffset
    
(* Internal invariants *)
INVARIANT Inv1 == (0 <= file_pointer <= MaxOffset) /\ (file_pointer = lo + Cardinality({i | i < hi AND buff[i] = disk(i)}))
INVARIANT Inv2 == (lo <= hi <= BuffSz) /\ (hi - lo = Cardinality({i | i < file_pointer AND buff[i] = ArbitrarySymbol}))
(* INVARIANT Inv2 *) (* see note at definition of Inv2 *)

DEFINE 
    restoreInvariantsAfterIncreasingCurr() == IF (file_pointer > 0) /\ (buff[file_pointer - 1] <> ArbitrarySymbol) THEN buff[file_pointer - 1] := disk(file_pointer - 1) ENDIF
    
OPERATIONS 
    FlushBuffer() == IF dirty THEN FORALL i IN lo..hi-1 DO buff[i] := disk(i + lo) ODENDIF
    Seek(pos) == lo := pos /\ hi := Max(lo, pos + BuffSz)
    
(* Properties *)
PROPERTY Inv2CanAlwaysBeRestored == (~dirty => ENABLED Seek(file_pointer)) /\ (Seek(file_pointer) => buff[file_pointer] = ArbitrarySymbol)
PROPERTY Safety == (lo <= hi <= MaxOffset) /\ ((hi - lo = Cardinality({i | i < file_pointer AND buff[i] = disk(i)})) IMPL Inv2)
(* The following properties are not defined in the Java RandomAccessFile contract *)
PROPERTY FlushBufferCorrect == (dirty => ENABLED FlushBuffer()) /\ (FlushBuffer() => FORALL i IN lo..hi-1 DO buff[i] = disk(i + lo) OD)
PROPERTY SeekCorrect == (~dirty => ENABLED Seek(file_pointer)) /\ (Seek(file_pointer) => file_pointer <= MaxOffset)
PROPERTY SeekEstablishesInv2 == (Seek(pos) => Inv2)
(* The following properties are not defined in the Java RandomAccessFile contract *)
PROPERTY Write1Correct == (* extend the file with ArbitrarySymbols if necessary, then overlay some data_to_write at the given offset. *)
PROPERTY Read1Correct == (* copy bytes from disk to memory and advance the pointer. *)
PROPERTY WriteAtMostCorrect == (* extend the file with ArbitrarySymbols if necessary, then overlay at most data_to_write at the given offset. *)
PROPERTY ReadCorrect == (* copy at most n bytes from disk to memory and advance the pointer. *)

=============================================================================
====