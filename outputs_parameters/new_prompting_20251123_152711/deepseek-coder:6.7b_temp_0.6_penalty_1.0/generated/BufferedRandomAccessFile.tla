---- MODULE BufferedRandomAccessFile ----

EXTENDS ModuleName

CONSTANTS
  Symbols = {A, B}
  ArbitrarySymbol = ArbitrarySymbol
  MaxOffset = 3
  BuffSz = 2

VARIABLES
  f :: File
  lo :: Offset
  hi :: Offset
  buff :: [BuffSz]Symbols
  curr :: Offset
  dirty :: BOOLEAN
  closed :: BOOLEAN

ASSIGN
  Inv1 == (0 <= lo <= hi <= MaxOffset) /\ (0 <= curr <= hi)
  Inv2 == (0 <= lo <= hi <= MaxOffset) /\ (0 <= curr <= hi) /\ (dirty ==> curr = lo)
  Inv3 == (0 <= lo <= hi <= MaxOffset) /\ (0 <= curr <= hi)
  Inv4 == (0 <= lo <= hi <= MaxOffset) /\ (0 <= curr <= hi)
  Inv5 == (0 <= lo <= hi <= MaxOffset) /\ (0 <= curr <= hi)

DEFINITIONS
  Inv2CanAlwaysBeRestored == (ENABLED FlushBuffer ==> ENABLED Seek(curr)) /\ (ENABLED Seek(curr) ==> Inv2')
  Safety == Inv1 /\ Inv2 /\ Inv3 /\ Inv4 /\ Inv5
  FlushBufferCorrect == (ENABLED FlushBuffer ==> dirty') /\ (~dirty ==> ENABLED FlushBuffer)
  SeekCorrect == (ENABLED Seek(curr) ==> (lo' = curr) /\ (hi' = Max(curr, hi)) /\ (dirty' = FALSE))
  SeekEstablishesInv2 == (ENABLED Seek(curr) ==> Inv2)
  Write1Correct == (ENABLED Write(data) ==> (file_content'[curr .. curr+len(data)-1] = data) /\ (curr' = curr + len(data)))
  Read1Correct == (ENABLED Read(len) ==> (data' = file_content[curr .. curr+len-1]) /\ (curr' = curr + len))
  WriteAtMostCorrect == (ENABLED WriteAtMost(data, len) ==> (file_content'[curr .. curr+len-1] = data) /\ (curr' = curr + len))
  ReadCorrect == (ENABLED Read(len) ==> (data' = file_content[curr .. curr+len-1]) /\ (curr' = curr + len))

SPECIFICATION Spec == ENABLED Safety /\ Safety'

====
====