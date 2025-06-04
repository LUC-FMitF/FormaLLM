----------------------- MODULE BufferedRandomAccessFile -----------------------

EXTENDS Naturals, Sequences, TLC, Common

CONSTANT BuffSz

VARIABLES

dirty,
length,
curr,
lo,
buff,
diskPos,

file_content,
file_pointer

vars == <<
dirty, length, curr, lo, buff, diskPos,
file_content, file_pointer>>

TypeOK ==
/\ dirty \in BOOLEAN
/\ length \in Offset
/\ curr \in Offset
/\ lo \in Offset
/\ buff \in Array(SymbolOrArbitrary, BuffSz)
/\ diskPos \in Offset

/\ file_content \in ArrayOfAnyLength(SymbolOrArbitrary)
/\ ArrayLen(file_content) <= MaxOffset
/\ file_pointer \in Offset

-------------------------------------------------------------------------------

RelevantBufferContent ==
ArraySlice(buff, 0, Min(BuffSz, length - lo))

LogicalFileContent ==
IF ArrayLen(RelevantBufferContent) > 0
THEN WriteToFile(file_content, lo, RelevantBufferContent)
ELSE file_content

DiskF(i) ==
IF i >= 0 /\ i < ArrayLen(file_content)
THEN ArrayGet(file_content, i)
ELSE ArbitrarySymbol

BufferedIndexes == lo .. (Min(lo + BuffSz, length) - 1)

Inv1 ==

/\ length = ArrayLen(LogicalFileContent)
/\ diskPos = file_pointer

Inv2 ==
/\ lo <= curr
/\ curr < lo + BuffSz

Inv3 ==
\A i \in BufferedIndexes:
ArrayGet(LogicalFileContent, i) = ArrayGet(buff, i - lo)

Inv4 ==
\A i \in 0 .. (length - 1):
i \notin BufferedIndexes =>
ArrayGet(LogicalFileContent, i) = DiskF(i)

Inv5 ==
(\E i \in BufferedIndexes: DiskF(i) /= ArrayGet(buff, i - lo)) =>
dirty

-------------------------------------------------------------------------------

Init ==
/\ dirty = FALSE
/\ length = 0
/\ curr = 0
/\ lo = 0
/\ buff \in Array({ArbitrarySymbol}, BuffSz)
/\ diskPos = 0
/\ file_pointer = 0
/\ file_content = EmptyArray

FlushBuffer ==
/\ dirty
/\ LET len == Min(length - lo, BuffSz) IN
/\ IF len > 0
THEN LET diskPosA == lo IN
/\ file_content' = WriteToFile(file_content, diskPosA, ArraySlice(buff, 0, len))
/\ file_pointer' = diskPosA + len
/\ diskPos' = lo + len
ELSE
UNCHANGED <<diskPos, file_pointer, file_content>>
/\ dirty' = FALSE
/\ UNCHANGED <<length, curr, lo, buff>>

FillBuffer ==
LET diskPosA == lo' IN
/\ buff' = MkArray(BuffSz, [i \in 0..BuffSz |->
LET fileOffset == diskPosA + i IN
IF fileOffset < ArrayLen(file_content)
THEN ArrayGet(file_content, fileOffset)
ELSE ArbitrarySymbol])
/\ file_pointer' = Min(diskPosA + BuffSz, ArrayLen(file_content))
/\ diskPos' = Min(diskPosA + BuffSz, ArrayLen(file_content))

Seek(pos) ==
/\ curr' = pos
/\ IF pos < lo \/ pos >= (lo + BuffSz) THEN
/\ ~dirty
/\ lo' = (pos \div BuffSz) * BuffSz
/\ FillBuffer
ELSE
UNCHANGED <<lo, diskPos, file_pointer, buff>>
/\ UNCHANGED <<dirty, length, file_content>>

SetLength(newLength) ==
/\ file_content' = TruncateOrExtendFile(file_content, newLength)
/\ IF ArrayLen(file_content) > newLength /\ file_pointer > newLength
THEN file_pointer' = newLength
ELSE file_pointer' \in Offset
/\ length' = newLength
/\ diskPos' = file_pointer'
/\ IF curr > newLength
THEN curr' = newLength
ELSE UNCHANGED curr

/\ buff' = MkArray(BuffSz, [i \in 0..(BuffSz-1) |->
IF lo + i < newLength
THEN ArrayGet(buff, i)
ELSE ArbitrarySymbol])
/\ UNCHANGED <<dirty, lo>>

Read1(byte) ==
/\ Inv2
/\ curr < length
/\ byte = ArrayGet(buff, curr - lo)
/\ curr' = curr + 1
/\ UNCHANGED <<lo, diskPos, buff, file_pointer, dirty, file_content, length>>

Write1(byte) ==
/\ curr + 1 <= MaxOffset
/\ Inv2
/\ buff' = ArraySet(buff, curr - lo, byte)
/\ curr' = curr + 1
/\ dirty' = TRUE
/\ length' = Max(length, curr')
/\ UNCHANGED <<lo, diskPos, file_pointer, file_content>>

Read(data) ==
LET numReadableWithoutSeeking == Min(lo + BuffSz, length) - curr IN
/\ Inv2
/\ numReadableWithoutSeeking >= 0
/\ LET
numToRead == Min(ArrayLen(data), numReadableWithoutSeeking)
buffOff == curr - lo
IN
/\ data = ArraySlice(buff, buffOff, buffOff + numToRead)
/\ curr' = curr + numToRead
/\ UNCHANGED <<buff, dirty, diskPos, file_content, file_pointer, length, lo>>

WriteAtMost(data) ==
LET
numWriteableWithoutSeeking == Min(ArrayLen(data), lo + BuffSz - curr)
buffOff == curr - lo
IN
/\ Inv2
/\ curr + numWriteableWithoutSeeking <= MaxOffset
/\ buff' = ArrayConcat(ArrayConcat(
ArraySlice(buff, 0, buffOff),
ArraySlice(data, 0, numWriteableWithoutSeeking)),
ArraySlice(buff, buffOff + numWriteableWithoutSeeking, ArrayLen(buff)))
/\ dirty' = TRUE
/\ curr' = curr + numWriteableWithoutSeeking
/\ length' = Max(length, curr')
/\ UNCHANGED <<lo, diskPos, file_content, file_pointer>>

Next ==
\/ FlushBuffer
\/ \E offset \in Offset:
\/ Seek(offset)
\/ SetLength(offset)
\/ \E symbol \in SymbolOrArbitrary:
\/ Read1(symbol)
\/ Write1(symbol)
\/ \E len \in 1..MaxOffset: \E data \in Array(SymbolOrArbitrary, len):
\/ WriteAtMost(data)
\/ Read(data)

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------

RAF == INSTANCE RandomAccessFile WITH
file_content <- LogicalFileContent,
file_pointer <- curr

Safety == RAF!Spec

FlushBufferCorrect  == [][FlushBuffer => UNCHANGED RAF!vars]_vars
SeekCorrect         == [][\A offset \in Offset: Seek(offset) => RAF!Seek(offset)]_vars
SetLengthCorrect    == [][\A offset \in Offset: SetLength(offset) => RAF!SetLength(offset)]_vars
SeekEstablishesInv2 == [][\A offset \in Offset: Seek(offset) => Inv2']_vars
Write1Correct       == [][\A symbol \in SymbolOrArbitrary: Write1(symbol) => RAF!Write(SeqToArray(<<symbol>>))]_vars
Read1Correct        == [][\A symbol \in SymbolOrArbitrary: Read1(symbol) => RAF!Read(SeqToArray(<<symbol>>))]_vars
WriteAtMostCorrect  == [][\A len \in 1..MaxOffset: \A data \in Array(SymbolOrArbitrary, len): WriteAtMost(data) => \E written \in 1..len: RAF!Write(ArraySlice(data, 0, written))]_vars
ReadCorrect         == [][\A len \in 1..MaxOffset: \A data \in Array(SymbolOrArbitrary, len): Read(data) => RAF!Read(data)]_vars

FlushBufferPossibleWhenDirty == dirty => ENABLED FlushBuffer
FlushBufferMakesProgress == [][FlushBuffer => ~dirty']_vars
SeekCurrPossibleWhenNotDirty == ~dirty => ENABLED Seek(curr)
SeekCurrRestoresInv2 == [][Seek(curr) => Inv2']_vars
Inv2CanAlwaysBeRestored ==
/\ []FlushBufferPossibleWhenDirty
/\ FlushBufferMakesProgress
/\ []SeekCurrPossibleWhenNotDirty
/\ SeekCurrRestoresInv2

-------------------------------------------------------------------------------

Symmetry == Permutations(Symbols)

Alias == [

BuffSz            |-> BuffSz,
MaxOffset         |-> MaxOffset,

dirty             |-> dirty,
length            |-> length,
curr              |-> curr,
lo                |-> lo,
buff              |-> buff,
diskPos           |-> diskPos,
file_content      |-> file_content,
file_pointer      |-> file_pointer,

abstract_contents |-> LogicalFileContent]

===============================================================================

--------------------------- MODULE RandomAccessFile ---------------------------

EXTENDS Naturals, Sequences, Common

VARIABLES
file_content,
file_pointer

vars == <<file_content, file_pointer>>

TypeOK ==
/\ file_content \in ArrayOfAnyLength(SymbolOrArbitrary)
/\ ArrayLen(file_content) <= MaxOffset
/\ file_pointer \in Offset

Init ==
/\ file_content = EmptyArray
/\ file_pointer = 0

Seek(new_offset) ==
/\ new_offset \in Offset
/\ file_pointer' = new_offset
/\ UNCHANGED <<file_content>>

SetLength(new_length) ==
/\ file_content' = TruncateOrExtendFile(file_content, new_length)

/\ IF ArrayLen(file_content) > new_length /\ file_pointer > new_length
THEN file_pointer' = new_length
ELSE file_pointer' \in Offset

Read(output) ==
/\ output = ArraySlice(file_content, file_pointer, Min(file_pointer + ArrayLen(output), ArrayLen(file_content)))
/\ file_pointer' = file_pointer + ArrayLen(output)
/\ UNCHANGED <<file_content>>

Write(data) ==
/\ file_pointer + ArrayLen(data) <= MaxOffset
/\ file_content' = WriteToFile(file_content, file_pointer, data)
/\ file_pointer' = file_pointer + ArrayLen(data)

Next ==
\/ \E offset \in Offset:
\/ Seek(offset)
\/ SetLength(offset)
\/ \E len \in 1..MaxOffset: \E data \in Array(SymbolOrArbitrary, len):
\/ Write(data)
\/ Read(data)

Spec == Init /\ [][Next]_vars

===============================================================================

-------------------------------- MODULE Common --------------------------------

EXTENDS Naturals, Sequences

CONSTANTS
Symbols,
ArbitrarySymbol,
MaxOffset

Offset == 0..MaxOffset

SymbolOrArbitrary == Symbols \union {ArbitrarySymbol}

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a <= b THEN b ELSE a

ArrayOfAnyLength(T) == [elems: Seq(T)]
Array(T, len) == [elems: [1..len -> T]]
ConstArray(len, x) == [elems |-> [i \in 1..len |-> x]]
MkArray(len, f) == [elems |-> [i \in 1..len |-> f[i - 1]]]
EmptyArray == [elems |-> <<>>]
ArrayLen(a) == Len(a.elems)
ArrayToSeq(a) == a.elems
SeqToArray(seq) == [elems |-> seq]
ArrayGet(a, i) == a.elems[i+1]
ArraySet(a, i, x) == [a EXCEPT !.elems[i+1] = x]
ArraySlice(a, startInclusive, endExclusive) == [elems |-> SubSeq(a.elems, startInclusive + 1, endExclusive)]
ArrayConcat(a1, a2) == [elems |-> a1.elems \o a2.elems]

WriteToFile(file, offset, data_to_write) ==
LET
file_len == ArrayLen(file)
data_len == ArrayLen(data_to_write)
length == Max(file_len, offset + data_len)
IN
MkArray(
length,
[i \in 0..(length-1) |->
CASE
i < offset -> IF i < file_len THEN ArrayGet(file, i) ELSE ArbitrarySymbol
[]
i >= offset /\ i < offset + data_len -> ArrayGet(data_to_write, i - offset)
[]
i >= offset + data_len -> ArrayGet(file, i)])

TruncateOrExtendFile(file, new_length) ==
IF new_length > ArrayLen(file)
THEN ArrayConcat(file, ConstArray(new_length - ArrayLen(file), ArbitrarySymbol))
ELSE ArraySlice(file, 0, new_length)

===============================================================================
