---- MODULE Alternate ----

(**************************************************************************)
(* A philosophically correct spec would actually be                    *)
(**************************************************************************)

CONSTANTS   Philosopher, Fork, Table, Chopstick, State
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Naturals
LOCAL INSTANCE Sequences

\* The set of all philosophers
Philosophers == {0 .. 4}

\* The set of all forks
Forks == {0 .. 4}

\* The set of all tables
Tables == {0 .. 4}

\* The set of all chopsticks
Chopsticks == {0 .. 4}

\* The set of all states
States == {0 .. 4}

\* The initial state
StateInit == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of picking up a fork
ActionPickupFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of putting down a fork
ActionPutdownFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of eating
ActionEat == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of thinking
ActionThink == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the chopstick
ActionGoToChopstick == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the fork
ActionGoToFork == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the philosopher
ActionGoToPhilosopher == <<
  Philosopher |-> 0,
  Fork |-> 0,
  Table |-> 0,
  Chopstick |-> 0
>>

\* The action of going to the table
ActionGoToTable == <<
  Philosopher |-> 0,
====