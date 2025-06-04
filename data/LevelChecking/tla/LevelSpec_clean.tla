----------------------------- MODULE LevelSpec ------------------------------

EXTENDS Integers, Sequences
-----------------------------------------------------------------------------

NumMax(i, j) == IF i > j THEN i ELSE j

SetMax(S) ==  IF S = {} THEN 0
ELSE CHOOSE x \in S : \A y \in S : x \geq y

RecordCombine(S, T) ==

LET rc(s, t) ==
[i \in (DOMAIN s) \cup (DOMAIN t) |-> IF i \in DOMAIN s THEN s[i]
ELSE t[i]]
IN  {rc(s, t) : s \in S, t \in T}
-----------------------------------------------------------------------------
CONSTANT  NodeId, Node

Null == CHOOSE n : n \notin NodeId

-----------------------------------------------------------------------------

Ref(str) == {id \in NodeId : Node[id].kind = str}

ModuleNodeId        == Ref("ModuleNode")
InstanceNodeId      == Ref("InstanceNodeId")
OpDefNodeId         == Ref("OpDefNode")
ConstantDeclNodeId  == Ref("ConstantDeclNode")
VariableDeclNodeId  == Ref("VariableDeclNode")
OpDeclNodeId        == ConstantDeclNodeId \cup VariableDeclNodeId
OpApplNodeId        == Ref("OpApplNode")
SubstitutionNodeId  == Ref("SubstitutionNode")
BoundSymbolNodeId   == Ref("BoundSymbolNode")
LetInNodeId         == Ref("LetInNode")
ValueNodeId         == Ref("ValueNode")
IdentifierNodeId    == Ref("IdentifierNode")
OpDefOrDeclNodeId   == OpDefNodeId \cup OpDeclNodeId
ExprNodeId          == OpApplNodeId \cup LetInNodeId  \cup ValueNodeId
\cup IdentifierNodeId
-----------------------------------------------------------------------------

LevelValue == 0..3

LevelConstraint == [param : ConstantDeclNodeId, level : LevelValue]

ArgLevelConstraint ==

[param : ConstantDeclNodeId,  idx : Nat \ {0},  level : LevelValue]

ArgLevelParam ==

[op : NodeId, idx : Nat \ {0}, param : NodeId]

MinLevelConstraint(id, LC) ==

IF \E lc \in LC : lc.param = id
THEN LET minLC == CHOOSE lc \in LC :
/\ lc.param = id
/\ \A olc \in LC :
(olc.param = id) => (olc.level \geq lc.level)
IN  minLC.level
ELSE 3

MaxArgLevelConstraints(id, ALC) ==

LET n == Node[id].numberOfArgs
minALC(i) ==
LET isALC(lc) == (lc.param = id) /\ (lc.idx = i)
IN  IF \E lc \in ALC : isALC(lc)
THEN LET max == CHOOSE lc \in ALC :
/\ isALC(lc)
/\ \A olc \in ALC :
isALC(olc) => (olc.level \leq lc.level)
IN  max.level
ELSE 0
IN [i \in 1..n |-> minALC(i)]

LevelConstraintFields ==

[levelParams         : SUBSET ConstantDeclNodeId,
levelConstraints    : SUBSET LevelConstraint,
argLevelConstraints : SUBSET ArgLevelConstraint,
argLevelParams      : SUBSET ArgLevelParam]
-----------------------------------------------------------------------------

ModuleNode ==

[kind : {"ModuleNode"},
isConstant : BOOLEAN,

opDecls : SUBSET OpDeclNodeId,

opDefs  : SUBSET OpDefNodeId,

instances : SUBSET InstanceNodeId,

innerModules : SUBSET ModuleNodeId,

theorems : SUBSET ExprNodeId,
assumes  : SUBSET ExprNodeId,

levelConstraints    : SUBSET LevelConstraint,
argLevelConstraints : SUBSET ArgLevelConstraint,
argLevelParams      : SUBSET ArgLevelParam]

OpDefOrDeclNodeFields ==

[name : STRING,

numberOfArgs : Nat,

level : LevelValue]

OpDeclNode ==

RecordCombine([kind : {"ConstantDeclNode", "VariableDeclNode"}],
OpDefOrDeclNodeFields)

OpDefNode ==

RecordCombine(
[kind : {"OpDefNode"},
params : Seq(ConstantDeclNodeId),

maxLevels : Seq(LevelValue),
weights   : Seq({0,1}),
minMaxLevel : Seq(Seq(LevelValue)),
opLevelCond : Seq(Seq(Seq(BOOLEAN))),

body : ExprNodeId \cup {Null},

substitution : SubstitutionNodeId],

RecordCombine(OpDefOrDeclNodeFields, LevelConstraintFields))

InstanceNode ==

[kind : {"InstanceNode"},
module : ModuleNodeId,

params : Seq(ConstantDeclNodeId),

substitution : SubstitutionNodeId ,

numberOfArgs : Nat,
levelConstraints    : SUBSET LevelConstraint,
argLevelConstraints : SUBSET ArgLevelConstraint,
argLevelParams      : SUBSET ArgLevelParam]

OpDefOrDeclNode == OpDefNode \cup OpDeclNode

OpApplNode ==

RecordCombine(
[kind : {"OpApplNode"},
operator : OpDefOrDeclNodeId,

args : Seq(ExprNodeId) \ {<<>>},

quantSymbols : SUBSET BoundSymbolNodeId,

level : LevelValue],
LevelConstraintFields)

SubstitutionNode ==

[kind    : {"SubstitutionNode"},
subFor  : Seq(OpDeclNodeId),
subWith : Seq(ExprNodeId)]

IdentifierNode ==

RecordCombine(
[kind : {"IdentifierNode"},
ref  : OpDefOrDeclNodeId \cup BoundSymbolNodeId,
level : LevelValue],
LevelConstraintFields)

BoundSymbolNode ==

[kind  : {"BoundSymbolNode"},
name  : STRING,
level : {0,1}]

LetInNode ==

RecordCombine(
[kind : {"LetInNode"},
opDefs    : SUBSET OpDefNodeId,
instances : SUBSET InstanceNodeId,

body : ExprNodeId,
level: LevelValue],
LevelConstraintFields)

ValueNode == RecordCombine(

[kind  : {"ValueNode"},
level : {0}],
LevelConstraintFields)

ExprNode == OpApplNode \cup LetInNode \cup ValueNode \cup IdentifierNode

SemNode ==

ModuleNode \cup OpDefOrDeclNode \cup InstanceNode \cup
ExprNode \cup SubstitutionNode \cup BoundSymbolNode

-----------------------------------------------------------------------------

TypeOK ==

/\ Node \in [NodeId -> SemNode]
/\ \A id \in NodeId :
LET n == Node[id]
IN  /\ (n \in OpDefNode) =>
/\ Len(n.maxLevels) = n.numberOfArgs
/\ Len(n.weights)   = n.numberOfArgs
/\ Len(n.params) = n.numberOfArgs
/\ Len(n.minMaxLevel) = n.numberOfArgs
/\ Len(n.opLevelCond) = n.numberOfArgs
/\ \A i \in 1..n.numberOfArgs :
/\ Len(n.minMaxLevel[i]) = Node[n.params[i]].numberOfArgs
/\ Len(n.opLevelCond[i]) = n.numberOfArgs
/\ \A j \in 1..n.numberOfArgs :
Len(n.opLevelCond[i][j]) =
Node[n.params[i]].numberOfArgs

/\ (n \in OpDeclNode) =>
/\ (n.kind = "ConstantDeclNode") => (n.level = 0)
/\ (n.kind = "VariableDeclNode") => /\ n.level = 1
/\ n.numberOfArgs = 0

/\ (n \in OpApplNode) =>
(Len(n.args) = Node[n.operator].numberOfArgs)

/\ (n \in SubstitutionNode) => (Len(n.subFor) = Len(n.subWith))

/\ (n \in InstanceNode) =>
/\ n.numberOfArgs = Len(n.params)
/\

LET mparamid ==

[i \in 1..Len(Node[n.substitution].subFor) |->
Node[n.substitution].subFor[i]]
M == Node[n.module]

IN  M.opDecls = {mparamid[i] : i \in 1..Len(mparamid)}

-----------------------------------------------------------------------------

IsOpArg(op, k) == Node[op.params[k]].numberOfArgs > 0

SubstituteInLevelConstraint(rcd, subst) ==

LET paramNums == 1..Len(subst.subFor)

ParamSubst(id) ==

IF \E i \in paramNums : subst.subFor[i] = id
THEN LET subExpNum == CHOOSE i \in paramNums : subst.subFor[i] = id
IN  Node[subst.subWith[subExpNum]].levelParams
ELSE {id}

IsOpParam(i) == Node[subst.subFor[i]].numberOfArgs > 0

argNums == 1..Len(subst.subFor)

SubOp(opid) ==

IF \E i \in paramNums : subst.subFor[i] = opid
THEN LET subExpNum ==
CHOOSE i \in paramNums : subst.subFor[i] = opid
IN  Node[subst.subWith[subExpNum]].ref
ELSE opid

IN  [levelParams |->
UNION {ParamSubst(id) : id \in rcd.levelParams},

levelConstraints |->

LET Sub(lc) ==

{[lc EXCEPT !.param = par] :
par \in ParamSubst(lc.param)}

ALP(i) ==

{alp \in rcd.argLevelParams : alp.op = subst.subFor[i]}

SubInALP(alp) ==

{[alp EXCEPT !.param = par] :
par \in ParamSubst(alp.param)}

SubALP(i) == UNION {SubInALP(alp) : alp \in ALP(i)}

LC(i, alp) ==

[param |-> alp.param,
level |->
Node[Node[subst.subWith[i]].ref].maxLevels[alp.idx]]

OpDefParams ==
{i \in paramNums : /\ IsOpParam(i)
/\ Node[subst.subWith[i]].ref \in
OpDefNodeId}
IN  UNION {Sub(lc) : lc \in rcd.levelConstraints}
\cup
UNION { {LC(i, alp) : alp \in SubALP(i)} : i \in OpDefParams },

argLevelConstraints |->

LET Sub(alc) ==

IF \E i \in 1..Len(subst.subFor) : subst.subFor[i] = alc.param
THEN LET subExpNum ==
CHOOSE i \in argNums :
subst.subFor[i] = alc.param
IN  IF Node[subst.subWith[subExpNum]].ref \in
OpDeclNodeId
THEN {[alc EXCEPT !.param =
Node[subst.subWith[subExpNum]].ref]}
ELSE {}
ELSE {alc}

SubParamALP(i) ==

{alp \in rcd.argLevelParams : alp.param = subst.subFor[i]}

ALC(alp, i) ==

IF SubOp(alp.op) \in OpDeclNodeId
THEN {[param |-> SubOp(alp.op),
idx   |-> alp.idx,
level |-> Node[subst.subWith[i]].level]}
ELSE {}

ALCSet(i) == UNION {ALC(alp, i) : alp \in SubParamALP(i)}

IN  UNION {Sub(alc) : alc \in rcd.argLevelConstraints}
\cup
UNION {ALCSet(i) : i \in paramNums},

argLevelParams |->

LET Sub(alp) ==

IF SubOp(alp.op) \in OpDeclNodeId
THEN {[alp EXCEPT !.op = SubOp(alp.op), !.param = pId] :
pId \in ParamSubst(alp.param)}
ELSE {}
IN  UNION {Sub(alp) : alp \in rcd.argLevelParams} ]

ReducedLevelConstraint(rcd, paramSet) ==

[rcd EXCEPT
!.levelParams = @ \ paramSet,
!.levelConstraints  = {lc \in @ : lc.param \notin paramSet},
!.argLevelConstraints = {alc \in @ : alc.param \notin paramSet},
!.argLevelParams = {alp \in @ : /\ alp.op \notin paramSet
/\ alp.param \notin paramSet}]

-----------------------------------------------------------------------------

ModuleNodeLevelCorrect(n) ==

LET defParams(opid) ==

{Node[opid].params[i] : i \in 1..Node[opid].numberOfArgs}

nonDefs == n.instances \cup n.theorems \cup n.assumes

allDefs == n.opDefs \cup nonDefs

IN  /\

\A id \in n.assumes : Node[id].level = 0

/\ n.levelConstraints =
UNION {Node[opid].levelConstraints : opid \in allDefs}

/\ n.argLevelConstraints =
UNION {Node[opid].argLevelConstraints : opid \in allDefs}

/\ n.argLevelParams =

(UNION {ReducedLevelConstraint(
Node[opid],
defParams(opid)).argLevelParams :
opid \in n.opDefs})
\cup
UNION {Node[opid].argLevelParams : opid \in nonDefs}

InstanceNodeLevelCorrect(n) ==

LET r == Len(Node[n.substitution].subWith)
mexp == [i \in 1..r |-> Node[Node[n.substitution].subWith[i]]]

paramIds == {n.params[i] : i \in 1..n.numberOfArgs}

redMexp ==

[i \in 1..r |-> ReducedLevelConstraint(mexp[i], paramIds)]
M == Node[n.module]

mparamId == [i \in 1..r |-> Node[n.substitution].subFor[i]]

mparam == [i \in 1..r |-> Node[mparamId[i]]]

mOpArg(i) == Node[mexp[i].ref]

subst == Node[n.substitution]

MSubConstraints ==

SubstituteInLevelConstraint(
[levelParams         |-> {op \in M.opDecls : Node[op].level = 0},
levelConstraints    |-> M.levelConstraints,
argLevelConstraints |-> M.argLevelConstraints,
argLevelParams      |-> M.argLevelParams],
subst)
redMSubConstraints ==

ReducedLevelConstraint(MSubConstraints, paramIds)

IN

/\

~M.isConstant =>
\A i \in 1..r : mexp[i].level \leq mparam[i].level

/\

\A i \in 1..r :
mexp[i].level \leq
MinLevelConstraint(mparamId[i], M.levelConstraints)

/\

\A i \in 1..r :
/\ mparam[i].numberOfArgs > 0
/\ mOpArg(i) \in OpDefNode

=>

\A j \in 1..mOpArg(i).numberOfArgs :
mOpArg(i).maxLevels[j] \geq
MaxArgLevelConstraints(mparamId[i],
M.argLevelConstraints)[j]
/\

\A alp \in M.argLevelParams :
\A i, j \in 1..r :
/\ alp.op    = mparamId[i]
/\ alp.param = mparamId[j]
/\ mOpArg(i) \in OpDefNode
=> (mexp[j].level \leq mOpArg(i).maxLevels[alp.idx])

/\ n.levelConstraints =
redMSubConstraints.levelConstraints \cup
UNION {redMexp[i].levelConstraints : i \in 1..r}
/\ n.argLevelConstraints =
redMSubConstraints.argLevelConstraints \cup
UNION {redMexp[i].argLevelConstraints : i \in 1..r}
/\ n.argLevelParams =
redMSubConstraints.argLevelParams \cup
UNION {redMexp[i].argLevelParams : i \in 1..r}

OpDefNodeLevelCorrect(n) ==

LET p == n.numberOfArgs
param == n.params
paramIds == {param[i] : i \in 1..p}

exp == Node[n.body]

subst == Node[n.substitution]
r == Len(Node[n.substitution].subWith)
iParamIds == {param[i] : i \in 1..r}

mparamId == Node[n.substitution].subFor

mexp == [i \in 1..r |-> Node[Node[n.substitution].subWith[i]]]

subExp == SubstituteInLevelConstraint(exp, subst)

IN  /\ n.level =

LET pLevel(i) == IF mparamId[i] \in subExp.levelParams
THEN mexp[i].level
ELSE 0
IN  NumMax(exp.level, SetMax({pLevel(i) : i \in 1..r}))

/\ n.maxLevels =

[i \in 1..p |->
MinLevelConstraint(
param[i],
subExp.levelConstraints \cup
UNION {mexp[j].levelConstraints : j \in 1..r})]

/\ n.weights =

[i \in 1..p |-> IF param[i] \in subExp.levelParams THEN 1 ELSE 0]

/\ n.minMaxLevel =

[i \in 1..p |->
MaxArgLevelConstraints(
param[i],
subExp.argLevelConstraints \cup
UNION {mexp[j].argLevelConstraints : j \in 1..r})]

/\ n.opLevelCond =

[i \in 1..p |->
[j \in 1..p |->
[k \in 1..Node[param[i]].numberOfArgs |->
[op |-> param[i], idx |-> k, param |-> param[j]]
\in subExp.argLevelParams \cup
UNION {mexp[h].argLevelParams : h \in 1..r}]]]

/\ n.levelParams = subExp.levelParams \ paramIds

/\ n.levelConstraints =

{lc \in subExp.levelConstraints : lc.param \notin paramIds}

/\ n.argLevelConstraints =

{alc \in subExp.argLevelConstraints : alc.param \notin paramIds }

/\ n.argLevelParams =

{alp \in subExp.argLevelParams : \/ alp.op    \notin paramIds
\/ alp.param \notin paramIds }
\cup
{alp \in UNION {mexp[j].argLevelParams : j \in 1..r}:
\/ /\ alp.op    \in    paramIds
/\ alp.param \notin paramIds
\/ /\ alp.op    \notin paramIds
/\ alp.param \in    paramIds }

DeclaredOpApplNodeLevelCorrect(n) ==

LET

p     == Len(n.args)
arg   == [i \in 1..p |-> Node[n.args[i]]]

opid == n.operator
op   == Node[opid]

param == op.params
IN  /\ n.level = NumMax(op.level,
SetMax({arg[i].level : i \in 1..p}))

/\ n.levelParams =

{opid} \cup UNION {arg[i].levelParams : i \in 1..p}

/\ n.levelConstraints =

UNION {arg[i].levelConstraints : i \in 1..p}

/\ n.argLevelConstraints =

{[op |-> opid, idx |-> i, level |-> arg[i].level] : i \in 1..p}
\cup
UNION {arg[i].argLevelConstraints : i \in 1..p}

/\ n.argLevelParams =

(LET ALP(i) ==

{[op |-> opid, idx   |-> i, param |-> par] :
par \in arg[i].levelParams}
IN  UNION {ALP(i) : i \in 1..p} )
\cup
UNION {arg[i].argLevelParams : i \in 1..p}

DefinedOpApplNodeLevelCorrect(n) ==

LET

p     == Len(n.args)
arg   == [i \in 1..p |-> Node[n.args[i]]]

op    == Node[n.operator]

param == op.params
numOpArgs(i) == Node[param[i]].numberOfArgs

defOpArgs ==

{i \in 1..p : IsOpArg(op, i) /\ (arg[i].ref \in OpDefNodeId)}
declOpArgs ==

{i \in 1..p : IsOpArg(op, i) /\ (arg[i].ref \in OpDeclNodeId)}
OpLevelCondIdx(i,j) ==

{k \in 1..Node[param[i]].numberOfArgs : op.opLevelCond[i][j][k]}
IN  /\

\A i \in 1..p :
/\ arg[i].level \leq op.maxLevels[i]

/\ /\ IsOpArg(op, i)

/\ arg[i].ref \in OpDefNodeId

=> /\

\A k \in 1.. numOpArgs(i) :
Node[arg[i].ref].maxLevels[k] \geq op.minMaxLevel[i][k]
/\

\A j \in 1..p :
\A k \in 1..numOpArgs(i) :
op.opLevelCond[i][j][k] =>
arg[j].level \leq arg[i].maxLevels[k]

/\ n.level =

NumMax(op.level,
SetMax({arg[i].level * op.weights[i] : i \in 1..p}))

/\ n.levelParams =

op.levelParams \cup
LET LP(i) == IF op.weights[i] = 1 THEN arg[i].levelParams
ELSE { }
IN  UNION {LP(i) : i \in 1..p}

/\ n.levelConstraints =

op.levelConstraints
\cup

(UNION {arg[i].levelConstraints : i \in 1..p})
\cup

(LET LC(i) == {[param |-> par, level |-> op.maxLevels[i]] :
par \in arg[i].levelParams}
IN  UNION {LC(i) : i \in 1..p})
\cup

(LET LC(i,j,k) ==

{[param |-> par, level |-> Node[arg[i].ref].maxLevels[k]] :
par \in arg[j].levelParams}
LCE(i,j) ==

UNION {LC(i,j,k) : k \in OpLevelCondIdx(i,j)}
IN  UNION {LCE(i,j) : i \in defOpArgs, j \in 1..p} )
\cup

(LET
ALP(i) ==

{alp \in op.argLevelParams : alp.op = param[i]}
LC(i) ==

{[param |-> alp.param,
level |-> Node[arg[i].ref].maxLevels[alp.idx]] :
alp \in ALP(i)}
IN  UNION {LC(i) : i \in defOpArgs} )

/\ n.argLevelConstraints =

op.argLevelConstraints
\cup

(UNION {arg[i].argLevelConstraints : i \in 1..p})
\cup

(LET
ALC(i) ==

{[param |-> arg[i].ref,
idx   |-> k,
level |-> op.minMaxLevel[i][k]] :
k \in 1..numOpArgs(i)}
IN  UNION {ALC(i) : i \in declOpArgs})
\cup

(LET ALC(i, j) ==

{[param |-> arg[i].ref,
idx |-> k,
level |-> arg[j].level] : k \in OpLevelCondIdx(i,j)}

IN  UNION {ALC(i,j) : i \in declOpArgs, j \in 1..p} )
\cup

(LET ALP(i) == {alp \in op.argLevelParams : alp.param = param[i]}

ALC(i) ==

{[param |-> alp.param,
idx   |-> alp.idx,
level |-> arg[i].level] : alp \in ALP(i)}
IN  UNION {ALC(i) : i \in 1..p})

/\ n.argLevelParams =

(UNION {arg[i].argLevelParams : i \in 1..p})
\cup

{alp \in op.argLevelParams :
\A i \in 1..p : (alp.op # param[i]) /\ (alp.param # param[i])}
\cup

(LET ALP(i) == {alp \in op.argLevelParams : alp.op = param[i]}

NLP(i) ==

{[alp EXCEPT !.op = arg[i].ref] : alp \in ALP(i)}
IN  UNION {NLP(i) : i \in declOpArgs})
\cup

(LET OLP(i) ==

{alp \in op.argLevelParams : alp.param = param[i]}
ALP(i) ==

{[alp EXCEPT !.param = par] :
alp \in OLP(i), par \in arg[i].levelParams}
IN  UNION {ALP(i) : i \in declOpArgs} )
\cup

(LET ALP(i,j) ==

{[op |-> arg[i].ref, idx |-> k, param |-> par] :
k \in OpLevelCondIdx(i,j), par \in arg[j].levelParams}
IN  UNION {ALP(i,j) : i \in declOpArgs, j \in 1..p})

OpApplNodeLevelCorrect(n) ==
IF n.operator \in OpDeclNodeId THEN DeclaredOpApplNodeLevelCorrect(n)
ELSE DefinedOpApplNodeLevelCorrect(n)

LetInNodeLevelCorrect(n) ==

LET exp    == Node[n.body]
letIds == n.opDefs \cup n.instances
opParams(opid) ==

{Node[opid].params[i] : i \in 1..Node[opid].numberOfArgs}
IN  /\ n.level = exp.level
/\ n.levelParams =
exp.levelParams
/\ n.levelConstraints =
exp.levelConstraints \cup
UNION {Node[opid].levelConstraints : opid \in letIds}
/\ n.argLevelConstraints =
exp.argLevelConstraints \cup
UNION {Node[opid].argLevelConstraints : opid \in letIds}
/\ n.argLevelParams =
exp.argLevelParams
\cup
(UNION {ReducedLevelConstraint(Node[opid],
opParams(opid)).argLevelParams :
opid \in n.opDefs})
\cup
UNION {Node[opid].argLevelParams : opid \in n.instances}

IdentifierNodeLevelCorrect(n) ==

/\ n.level = Node[n.ref].level

/\ IF n.ref \in OpDeclNodeId \cup BoundSymbolNodeId
THEN

/\ n.levelParams         = IF n.ref \in ConstantDeclNodeId
THEN {n.ref}
ELSE { }
/\ n.levelConstraints    = { }
/\ n.argLevelConstraints = { }
/\ n.argLevelParams      = { }

ELSE

/\ n.levelParams         = Node[n.ref].levelParams
/\ n.levelConstraints    = Node[n.ref].levelConstraints
/\ n.argLevelConstraints = Node[n.ref].argLevelConstraints
/\ n.argLevelParams      = Node[n.ref].argLevelParams

LevelCorrect ==

\A id \in NodeId :
LET n == Node[id]
IN  /\ (n \in IdentifierNode) => IdentifierNodeLevelCorrect(n)
/\ (n \in OpApplNode)     => OpApplNodeLevelCorrect(n)
/\ n \in LetInNode        => LetInNodeLevelCorrect(n)
/\ n \in InstanceNode     => InstanceNodeLevelCorrect(n)
/\ n \in ModuleNode       => ModuleNodeLevelCorrect(n)
/\ (n \in OpDefNode) /\ (n.body # Null) => OpDefNodeLevelCorrect(n)

=============================================================================
