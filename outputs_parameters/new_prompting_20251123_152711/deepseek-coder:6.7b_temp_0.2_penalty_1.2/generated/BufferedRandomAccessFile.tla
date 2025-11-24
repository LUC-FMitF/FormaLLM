---- MODULE BufferedRandomAccessFile ----

EXTENDS ModuleName

CONSTANTS
  Symbols = {A, B}
  ArbitrarySymbol = ArbitrarySymbol
  MaxOffset = 3
  BuffSz = 2

VARIABLES
  file_content, file_pointer, buff, lo, hi, dirty

ASSUME
  file_content \in Seq(Symbols)
  file_pointer \in 0..MaxOffset
  buff \in Seq(Symbols)
  lo, hi \in 0..MaxOffset
  dirty \in {TRUE, FALSE}

DEFINITIONS
  Inv1 == file_pointer <= Len(file_content)
  Inv2 == lo <= hi
  Inv3 == lo = 0 \/ hi = Len(file_content)
  Inv4 == lo <= file_pointer <= hi
  Inv5 == file_pointer = hi + 1 - Len(buff)

  Inv2CanAlwaysBeRestored ==
    [~dirty -> file_pointer = lo] /\
    [dirty -> file_pointer = hi + 1]

  Safety ==
    [Inv1 /\ Inv2 /\ Inv3 /\ Inv4 /\ Inv5]

  FlushBufferCorrect ==
    [dirty -> file_content' = [0..(lo-1) -> file_content[i], lo..hi -> buff, hi+1..Len(file_content) -> file_content[i]]]

  SeekCorrect ==
    [~dirty -> file_pointer' = file_pointer + Len(buff)]

  SeekEstablishesInv2 ==
    [~dirty -> Inv2']

  Write1Correct ==
    [file_pointer + Len(buff) <= MaxOffset ->
      file_content' = [0..file_pointer -> file_content[i], file_pointer..MaxOffset -> buff[i]]]

  Read1Correct ==
    [file_pointer + Len(buff) <= MaxOffset ->
      [buff[i] = file_content[file_pointer + i]]_{i \in 0..Len(buff)}]

  WriteAtMostCorrect ==
    [file_pointer + Len(buff) <= MaxOffset ->
      file_content' = [0..file_pointer -> file_content[i], file_pointer..file_pointer + Len(buff) -> buff[i]]]

  ReadCorrect ==
    [file_pointer + Len(buff) <= MaxOffset ->
      [buff[i] = file_content[file_pointer + i]]_{i \in 0..Len(buff)}]

SPECIFICATION Spec == Safety /\ FlushBufferCorrect /\ SeekCorrect /\ SeekEstablishesInv2 /\ Write1Correct /\ Read1Correct /\ WriteAtMostCorrect /\ ReadCorrect

====
CONSTANTS
  Symbols = {A, B}
  ArbitrarySymbol = ArbitrarySymbol
  MaxOffset = 3
  BuffSz = 2

SPECIFICATION Spec
INVARIANTS Safety, Inv1, Inv2, Inv3, Inv4, Inv5
PROPERTIES FlushBufferCorrect, SeekCorrect, SeekEstablishesInv2, Write1Correct, Read1Correct, WriteAtMostCorrect, ReadCorrect
====