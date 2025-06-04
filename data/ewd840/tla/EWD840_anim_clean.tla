------------------------------- MODULE EWD840_anim -------------------------------
EXTENDS EWD840, SVG, TLC, Sequences, Integers

VARIABLES history

AnimInit ==
/\ active \in [Node -> BOOLEAN]
/\ color \in [Node -> Color]
/\ tpos = N - 1
/\ tcolor = "black"
/\ history = <<0, 0, "init">>

AnimInitiateProbe ==
/\ InitiateProbe
/\ history' = <<history[1], history[2], "InitiateProbe">>

AnimPassToken(i) ==
/\ PassToken(i)
/\ history' = <<history[1], history[2], "PassToken">>

AnimSystem ==
/\ AnimInitiateProbe \/ \E i \in Node \ {0} : AnimPassToken(i)

AnimSendMsg(i) ==
/\ active[i]
/\ \E j \in Node \ {i} :
/\ active' = [active EXCEPT ![j] = TRUE]
/\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
/\ history' = <<i, j, "SendMsg">>
/\ UNCHANGED <<tpos, tcolor>>

AnimDeactivate(i) ==
/\ Deactivate(i)
/\ history' = <<history[1], history[2], "Deactivate">>

AnimEnvironment == \E i \in Node : AnimSendMsg(i) \/ AnimDeactivate(i)

AnimNext == AnimSystem \/ AnimEnvironment

Animvars == <<active, color, tpos, tcolor, history>>

AnimSpec == AnimInit /\ [][AnimNext]_Animvars /\ WF_Animvars(AnimSystem)

---------------------------------------------------------------------------
Arial == [font |-> "Arial"]

LegendBasePos == [ x |-> -5, y |-> 25 ]

RingBasePos == [w |-> 55, h |-> 55, r |-> 75]

TokenBasePos == [ w |-> RingBasePos.w + 12,
h |-> RingBasePos.h + 12,
r |-> RingBasePos.r + 25 ]

---------------------------------------------------------------------------

Labels == Group(<<Text(LegendBasePos.x, LegendBasePos.y, "Circle: Active, Black: Tainted", Arial),
Text(LegendBasePos.x, LegendBasePos.y + 20, "Line: Message, Arrow: Receiver", Arial),
Text(LegendBasePos.x, LegendBasePos.y + 40, "Level: " \o ToString(TLCGet("level")), Arial)>>,
<<>>)

---------------------------------------------------------------------------
NodeDimension == 26

RingNetwork ==
LET RN[ n \in Node ] ==
LET coord == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, n, N)
id == Text(coord.x + 10, coord.y - 5, ToString(n), Arial)
node == Rect(coord.x, coord.y, NodeDimension, NodeDimension,

[rx |-> IF ~active[n] THEN "0" ELSE "15",
stroke |-> "black",
fill |-> color[n]])
IN Group(<<node, id>>, ("transform" :> "translate(0 125)"))
IN Group(RN, <<>>)

---------------------------------------------------------------------------

TokenNetwork ==
LET coord == NodeOfRingNetwork(TokenBasePos.w, TokenBasePos.h, TokenBasePos.r, tpos, N)
circ  == Circle(coord.x, coord.y, 5, [stroke |-> "black", fill |-> tcolor])

IN Group(<<circ>>, ("transform" :> "translate(0 125)"))

---------------------------------------------------------------------------

ArrowPosOffset == NodeDimension \div 2

Messages ==
LET from == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, history[1], N)
to   == NodeOfRingNetwork(RingBasePos.w, RingBasePos.h, RingBasePos.r, history[2], N)
line == Line(from.x + ArrowPosOffset, from.y + ArrowPosOffset,
to.x + ArrowPosOffset, to.y + ArrowPosOffset,
[stroke |-> "orange", marker_end |-> "url(#arrow)"])
IN Group(IF history[3] = "SendMsg" THEN <<line>> ELSE <<>>, ("transform" :> "translate(0 125)"))

---------------------------------------------------------------------------

Defs ==
"<defs><marker id='arrow' markerWidth='15' markerHeight='15' refX='0' refY='3' orient='auto' markerUnits='strokeWidth' viewBox='0 0 20 20'><path d='M0,0 L0,6 L9,3 z' fill='orange' /></marker></defs>"

Animation == SVGElemToString(Group(<<Labels, RingNetwork, TokenNetwork, Messages>>, <<>>))

Alias == [

eyeofgnome |-> "<svg viewBox='-80 0 300 300'>" \o Defs \o Animation \o "</svg>"

]

---------------------------------------------------------------------------

AnimInv == terminationDetected => TLCGet("level") < 20

=============================================================================

## Assuming the most recent Toolbox nightly build (https://nightly.tlapl.us/dist)
## installed to /opt/toolbox.  On macOS, install gawk with `brew install gawk`
## (default nawk does not like the match).

/opt/toolbox/tla2tools.jar -simulate EWD840_anim | gawk 'match($0,/<svg.*<\/svg>/) { n += 1; print substr($0,RSTART,RLENGTH) > sprintf("%03d", n) ".svg" }' && eog .

## The best viewer for a stack of SVGs is Gnome's Eye Of Gnome (eog) that
## is available for Win, macOS, and Linux.  In its preferences, one can replace
## the transparent background with a custom color. One can also run a slideshow
## with a custom frame rate.

----

## Unfortunately, the MacPorts package cannot be easily installed because of the
## broken dependency https://trac.macports.org/ticket/61713 (see below).  Instead,
## one can use the browser-based TLA+ trace Animator at https://animator.tlapl.us.
## In this case, a slightly different awk matching is needed.  Optionally, pipe
## output of awk directly to xclip to send it to the clipboard ("| xclip").

/opt/toolbox/tla2tools.jar -simulate EWD840_anim | gawk 'match($0,/toolbox = .*/) { print "[\ntb |->" substr($0, RSTART+9, RLENGTH) "\n]," }'

## Technical notes:
## RSTART+9 removes "toolbox =".  Instead, prefix the match with "tb |->"
## that is expected by the TLA+ trace Animator.  Also, the definition
## of Messages above has been changed to not use SVG's visibility tag that
## causes problems with the TLA+ trace Animator and inkscape (see below).

----
## Install eog on macOS Big Sur x86_64 (doesn't work on arm64):
## a) `port install gupnp-igd` until it fails
## b) Patch `configure` according to https://trac.macports.org/ticket/61713#comment:5
## c) Rerun `port install gupnp-igd` with patched `configure`
## d) `port install neon configure.cflags=-Wno-error=all according to https://trac.macports.org/ticket/61483#comment:14
## e) `port install eog`
## f) `port install xorg-server`
## g) Run X server with `X` and open `eog` in a second terminal

----
## The commands below here have multiple issues such as broken aspect ratio,
## wrong dimensions, ...  Most importantly though, inkscape *ignores* SVG's
## visibility attribute causing a bogus animation.  However, the spec above
## no longer uses visibility=hidden in the definition of Message.

## Render as gif (shows without download when clicked in the Github repo)

convert -delay 100 -density 200 *.svg EWD840.gif

## Technical notes:
## convert ticks 100 times per second, thus, shows one svg per second.
## -density 200 determines the quality and produces approximately a gif
## with 600x600 dimensions. One has to increase the limits for ImageMagic
## in /etc/ImageMagic-6/policy.xml according to
## https://github.com/ImageMagick/ImageMagick/issues/396#issuecomment-501164036
## to keep it from choking.

## Render to mp4:
## The svgs have transparent background.  Convert them into pngs with a
## suitable resolution for the video while adding a white background.
#for i in *.svg; do convert -density 1000 -resize 1920x1080 $i $i.png; done

## contrary to convert above, this replaces the transparent background
## with a lightyellow one.
for i in *.svg; do inkscape -w 1920 -h 1920 -b lightyellow --export-png=$i.png $i; done

## Technical note:  Handling of the visibility tag in SVG is broken causing
## visibility=hidden to be ignored:
## - https://gitlab.com/inkscape/inbox/-/issues/2177
## - https://bugs.launchpad.net/inkscape/+bug/166042
## - https://bugs.launchpad.net/inkscape/+bug/1577763

## Render the sequence of pngs into an mp4 with two frames per second.
ffmpeg -r 2 -y -i %03d.svg.png EWD840.mp4

## https://stackoverflow.com/a/25002372/6291195 partially gets the job done of
## rendering an mp4 from the stack of SVGs (no png conversion needed).  It
## replaces the transparent background with a white one, but the dimensions
## are completely screwed up.
