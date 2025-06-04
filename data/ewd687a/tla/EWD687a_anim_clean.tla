---------------------------- MODULE EWD687a_anim ---------------------------
EXTENDS EWD687a, Integers, Sequences, SVG, TLC, IOUtils

Repeat(str, n) ==

LET R[ i \in 0..n ] ==
IF i = 0 THEN ""
ELSE R[i-1] \o str
IN R[n]

----------------------------------------------------------------------------

SVGDefs ==

"<defs><marker id='arrow' markerWidth='35' markerHeight='35' refX='14' refY='3' orient='auto' markerUnits='strokeWidth' viewBox='0 0 20 20'><path d='M0,0 L0,6 L9,3 z' fill='black' /></marker></defs>"

----------------------------------------------------------------------------

Legend ==

LET BasePos == [ x |-> 350, y |-> 120 ]

Action == TLCGet("action").name \o ToString(TLCGet("action").context) IN
Group(<<Text(BasePos.x, BasePos.y, "Step: " \o ToString(TLCGet("level")), <<>>),
Text(BasePos.x, BasePos.y + 20, "A:  " \o Action, <<>>),
Text(BasePos.x, BasePos.y + 40, "A': " \o Action', <<>>),
Text(BasePos.x, BasePos.y + 60, "~neutral procs red, round when also active", <<>>)>>,
<<>>)

----------------------------------------------------------------------------

NodeDimension ==
32

ArrowPosOffset ==

NodeDimension \div 2

GraphNodePos ==

NodesOfDirectedMultiGraph(Procs, Edges,
[algo |-> "Sugiyama",
view_width |-> 1000, view_height |-> 1800, layering |-> "LONGEST_PATH",
node_width |-> NodeDimension * 3, node_height |-> NodeDimension * 3])

----------------------------------------------------------------------------

N ==

LET NS[ p \in Procs ] ==
LET coord == GraphNodePos[p]
id == Text(coord.x + ArrowPosOffset - 5, coord.y + ArrowPosOffset + 7,
ToString(p), [fill |-> "white"])
node == Rect(coord.x, coord.y, NodeDimension, NodeDimension,

[ rx |-> IF active[p] THEN "15" ELSE "0",
fill |-> IF ~neutral(p) THEN "red" ELSE "black" ])
IN Group(<<node, id>>, <<>>)
IN Group(NS, <<>>)

E ==

LET ES[ e \in Edges ] ==
LET from == GraphNodePos[e[1]] to == GraphNodePos[e[2]]

mpt == PointOnLine(from, to, 2)
messages == Text(mpt.x, mpt.y,
Repeat("m", msgs[e]) \o Repeat("a", acks[e]), <<>>)

fpt == PointOnLine(from, to, 4)
sent == Text(fpt.x, fpt.y,
IF sentUnacked[e] > 0 THEN ToString(-1 * sentUnacked[e]) ELSE "",
<<>>)

tpt == PointOnLine(to, from, 4)
rcvd == Text(tpt.x, tpt.y,
IF rcvdUnacked[e] > 0 THEN ToString(rcvdUnacked[e]) ELSE "",
<<>>)
line == Line(from.x + ArrowPosOffset, from.y + ArrowPosOffset,
to.x + ArrowPosOffset, to.y + ArrowPosOffset,

[ stroke |-> "black", stroke_width |-> "2",
marker_end |-> "url(#arrow)" ])
IN Group(<<line, messages, sent, rcvd>>, <<>>)
IN Group(ES, <<>>)

U ==

LET UE[ u \in {upEdge[p] : p \in DOMAIN upEdge} \ {NotAnEdge} ] ==
LET from == GraphNodePos[u[1]] to == GraphNodePos[u[2]]
line == Line(from.x + ArrowPosOffset, from.y + ArrowPosOffset,
to.x + ArrowPosOffset, to.y + ArrowPosOffset,

[stroke |-> "orange", stroke_dasharray |-> "5", stroke_width |-> "5"])
IN Group(<<line>>, <<>>)
IN Group(UE, <<>>)

Frame ==

SVGDefs \o SVGElemToString(Group(<<Legend, E, U, N>>, <<>>))

----------------------------------------------------------------------------

ToFile(str, prefix, n, padding, suffix) ==

IOExecTemplate(

<<"bash", "-c", "echo \"%1$s\" > %2$s$(printf %%0%4$sd %3$s)%5$s">>,
<<str, prefix, ToString(n), ToString(padding), suffix>>)

Alias == [

_animator |->
Frame
,

file |->

ToFile("<svg viewBox='0 0 1400 1200'>" \o Frame \o "</svg>", "EWD687a_anim_", TLCGet("level"), 3, ".svg")
]

----------------------------------------------------------------------------

InterestingBehavior ==

TLCGet("level") > 20 => ~neutral(Leader)

NoSuperfluousIdleSteps ==

~UNCHANGED vars

----------------------------------------------------------------------------

CONSTANTS L, P1, P2, P3, P4, P5

Network ==
{ <<L, P1>>, <<L, P2>>, <<L, P3>>,
<<P1, P2>>, <<P1, P4>>,
<<P2, P3>>, <<P2, P5>>,
<<P4, P3>>, <<P4, P5>>,
<<P3, P1>>, <<P3, P5>>,
<<P5, P4>>}

NodesOfNetwork ==
{ e[1] : e \in Network } \cup { e[2] : e \in Network }

----------------------------------------------------------------------------
=============================================================================
