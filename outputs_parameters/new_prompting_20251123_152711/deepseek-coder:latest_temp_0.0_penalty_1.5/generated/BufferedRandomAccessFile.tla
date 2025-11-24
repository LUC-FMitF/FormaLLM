---- MODULE BufferedRandomAccessFile ----
(**************************************************************************)
(* TLC Configuration:                                                     *)
(**************************************************************************)

CONSTANTS 
  Symbols = {A, B}
  ArbitrarySymbol = ANY Symbols
  MaxOffset = 3
  BuffSz = 2

SYMMETRY Symmetry
  ALIAS Alias

INVARIANT TypeOK
INVARIANT Inv1
INVARIANT Inv2
INVARIANT Inv3
INVARIANT Inv4
INVARIANT Inv5
PROPERTY Inv2CanAlwaysBeRestored
INVARIANT Inv6
INVARIANT Inv7
INVARIANT Inv8
PROPERTY Safety
PROPERTY FlushBufferCorrect
PROPERTY SeekCorrect
PROPERTY SeekEstablishesInv2
PROPERTY Write1Correct
PROPERTY Read1Correct
PROPERTY WriteAtMostCorrect
PROPERTY ReadCorrect

(**************************************************************************)
(* BufferedRandomAccessFile Module:                                        *)
(**************************************************************************)

DEFINITIONS
  BufferedRandomAccessFile(f, file, data_content, file_content, 
  file_pointer, buff, closed, curr)
    f == TLC.File[file, data_content, file_pointer, buff, closed, curr]
    TLC.File[file, data_content, file_pointer, buff, closed, curr]
    data_content == {A, B}^(MaxOffset - 1)
    file_content == data_content^(MaxOffset - 1)
    file_pointer == (Alias(file_pointer))
    buff == {A, B}^(BuffSz - 1)
    closed == (f == EMPTY)
    curr == (f == EMPTY)

(**************************************************************************)
(* Specifications:                                                         *)
(**************************************************************************)

SPECIFICATION Spec
  CONSTANT Symbols = {A, B}
  CONSTANT ArbitrarySymbol = ANY Symbols
  CONSTANT MaxOffset = 3
  CONSTANT BuffSz = 2

  (* Invariants *)
  INVARIANT TypeOK
  INVARIANT Inv1
  INVARIANT Inv2
  INVARIANT Inv3
  INVARIANT Inv4
  INVARIANT Inv5
  PROPERTY Inv2CanAlwaysBeRestored
  INVARIANT Inv6
  INVARIANT Inv7
  INVARIANT Inv8

  (* Properties *)
  PROPERTY Safety
  PROPERTY FlushBufferCorrect
  PROPERTY SeekCorrect
  PROPERTY SeekEstablishesInv2
  PROPERTY Write1Correct
  PROPERTY Read1Correct
  PROPERTY WriteAtMostCorrect
  PROPERTY ReadCorrect

  (* Operations *)
  BACKUP (Super.Seek)
  OPERATION Seek(f, lo)
    INVARIANT Inv1
    OUTPUT c == (f.curr == lo)
    INVARIANT Inv2

  (* Definitions *)
  DEFINITIONS
    Seek(f, lo)
      INPUT c
      OUTPUT f.curr == lo

  BACKUP (Super.SetLength)
  OPERATION SetLength(f, len)
    INVARIANT Inv3
    OUTPUT f.curr == f.curr

  OPERATION Write(f, offset, data)
    INVARIANT Inv4
    INPUT c
    OUTPUT f.curr == (c AND offset)

  OPERATION Read(f, offset, len)
    INVARIANT Inv5
    INPUT c
    OUTPUT f.curr == (c AND offset)

  BACKUP (Super.Write)
  OPERATION Write(f, data)
    INVARIANT Inv6
    INPUT c
    OUTPUT f.curr == (c AND data)

  OPERATION Read(f, len)
    INVARIANT Inv7
    INPUT c
    OUTPUT f

  BACKUP (Super.FlushBuffer)
  OPERATION FlushBuffer(f)
    INVARIANT Inv8
    OUTPUT f.curr == f.curr

  OPERATION SetLength(f, len)
    INVARIANT Inv1
    OUTPUT f.curr == f.curr

  OPERATION Seek(f, offset)
    INVARIANT Inv1
    OUTPUT f.curr == offset

This module covers the core fields as well as the seek, read, write, flush,
and setLength operations. The BufferedRandomAccessFile module contains
all definitions and specifications related to the file. It uses 0-indexed
arrays as opposed to TLA+ 1-indexed sequences.
====