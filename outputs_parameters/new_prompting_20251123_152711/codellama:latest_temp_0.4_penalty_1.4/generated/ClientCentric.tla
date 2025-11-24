---- MODULE ClientCentric ----

\* A database `State` is represented by keys with corresponding values. *\/
CONSTANT Keys == <<>> : SET OF INTEGER
/\ InitValue \in Values /\ PrintT(<<k,v|->InitValue >>) => TRUE
LOCAL Operations == {Read |-> [Key], Write -> [Key]} /\ Reads <- [] /\ Writes <- {}
\/ (key: Keys) => key IN DOMAIN State ==> State[key] = InitValue
/\ PrintT(State) => \A Key \in Keys : TRUE
LOCAL Transactions == <<>> : SET OF TRANSACTION /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (transaction: Transactions) => \A Key \in Keys : TRUE
LOCAL TimeStamps == <<>> : SET OF TIMESTAMP /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (timestamp: TimeStamps) => \A Key \in Keys : TRUE
LOCAL Values == <<>> : SET OF INTEGER /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (value: Values) => value = InitValue ==> \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState] /\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransaction <- {}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptyTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (commitTest: CommitTests) => \A Key \in Keys : TRUE
LOCAL IsolationLevels == <<>> : SET OF ISOLATIONLEVEL /. ExecutionElem -> [parentState, transaction, resultState]/\ ReadStatesForEmptyTransaction <- {} /\ WriteSetForEmptYTransactioN<-{}
\/ (isolevel: IsolationLevels) => \A Key \in Keys : TRUE
LOCAL CommitTests == <<>> : SET OF COMMITTEST /. ExecutionElem -> [parentState, transaction, resultState]
====