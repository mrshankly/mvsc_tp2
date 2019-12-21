---------------------------- MODULE LeaderElection -----------------------------
(******************************************************************************)
(* Trabalho Prático 2 - MVSC 2019                                             *)
(*                                                                            *)
(* Realizado por:                                                             *)
(*     João Marques - 48500,                                                  *)
(*     Vicente Almeida - 47803                                                *)
(*                                                                            *)
(* In the following TLA file we specify a solution to the Leader Election     *)
(* problem, based on the improved version of the Dolev-Klawe-Rodeh algorithm. *)
(*                                                                            *)
(* Given a number of processes, this algorithms specifies an efficient way to *)
(* collectively find and establish which is the highest value contained       *)
(* within a process. We apply this to our problem by approaching the          *)
(* processe's values as their ids, so we would be electing the process with   *)
(* the highest id as the leader.                                              *)
(*                                                                            *)
(* The processes are arranged in a unidirectional circle (ring), so each one  *)
(* only communicates with it's right neighbour and receives messages only     *)
(* from its left neighbour. This communication is done by the exchange of two *)
(* kinds of messages, M1 and M2, in phases. Each process can be in one of     *)
(* three states: active, waiting or passive. Active processes can only        *)
(* receive M1 messages, while waiting and passive processes can receive both. *)
(* Ideally, at the end of each phase the processes progressively converge on  *)
(* the same id until a process receives a message with its id attached,       *)
(* signaling that the algorithm has succesfuly reached it's end.              *)
(*                                                                            *)
(* The actions implemented below follow the structure of the pseudo-code      *)
(* presented in the article by its authors. There are two actions for each    *)
(* state a process can have.                                                  *)
(******************************************************************************)

EXTENDS FiniteSets, Integers, Naturals, Sequences

CONSTANT MAX_PROCESSES, ID

(******************************************************************************)
(* Set of processes, where each process is identified by an integer ranging   *)
(* from 1 to MAX_PROCESSES.                                                   *)
(******************************************************************************)
processes == 1..MAX_PROCESSES

ASSUME
    MAX_PROCESSES > 1

ASSUME
    ID \in Seq(Int) /\ Len(ID) = MAX_PROCESSES

(******************************************************************************)
(* Represents the right neighbour or a given process p.                       *)
(******************************************************************************)
neighbour(p) == 1 + (p % MAX_PROCESSES)

(******************************************************************************)
(* Sets of all messages of type M1 and M2, as described in the article.       *)
(******************************************************************************)
message1 == [type: {1}, number: Int, phase: Nat, counter: Nat]
message2 == [type: {2}, number: Int]

--------------------------------------------------------------------------------

VARIABLES
    phase,      \* - The phase in which each process currently is.
    started,    \* - Indicates whether an active process has sent the initial M1
                \*   message to its neighbour in its current phase.
    state,      \* - State of a process, it can be active, waiting or passive.
    id,         \* - The number originally stored by a process.
    max,        \* - The accumulated maximum number stored by a process.
    terminated, \* - Flag indicating whether the algorithm has terminated or not.
    queue       \* - A function from processes to a sequence, where queue[p]
                \*   representes the sequence of messages (preserves order) that
                \*   a process p has received from its left neighbour.

vars == <<phase, started, state, id, max, queue, terminated>>

--------------------------------------------------------------------------------

TypeInvariant ==
    /\ phase \in [processes -> Nat]
    /\ started \in [processes -> BOOLEAN]
    /\ state \in [processes -> {"active", "waiting", "passive"}]
    /\ id \in [processes -> Int]
    /\ max \in [processes -> Int]
    /\ queue \in [processes -> Seq(message1 \union message2)]
    /\ terminated \in BOOLEAN

--------------------------------------------------------------------------------

Init ==
    /\ phase = [p \in processes |-> 0]
    /\ started = [p \in processes |-> FALSE]
    /\ state = [p \in processes |-> "active"]
    /\ id = [p \in processes |-> ID[p]]
    /\ max = id
    /\ queue = [p \in processes |-> <<>>]
    /\ terminated = FALSE

(***************************************************************************)
(* The process "p" sends an M1 type message to it's right neighbour.       *)
(* - Only active processes can perform this action.                        *)
(* - Exactly one M1 message should be sent by the process, per phase. This *)
(*   is ensured by the use of the variable started[p].                     *)
(***************************************************************************)
ActiveSendM1(p) ==
    /\ state[p] = "active" /\ started[p] = FALSE
    /\ started' = [started EXCEPT ![p] = TRUE]
    /\ LET msg == [
               type    |-> 1,
               number  |-> max[p],
               phase   |-> phase[p],
               counter |-> 2^(phase[p])
           ]
       IN queue' = [queue EXCEPT ![neighbour(p)] = Append(@, msg)] \* send message to neighbour
    /\ UNCHANGED <<phase, state, id, max, terminated>>

(***************************************************************************)
(* The active process "p" receives an M1 type message "m1".                *)
(*                                                                         *)
(* - If the number "n" contained within m1 is larger than p's current      *)
(*   maximum number then n shall become p's new maximum number. After      *)
(*   receiving this message p is now waiting for another message.          *)
(*                                                                         *)
(* - If n is smaller than p's maximum number then p will send an M2 type   *)
(*   message to it's neighbor, transmiting p's maximum number. After doing *)
(*   so, p becomes passive.                                                *)
(*                                                                         *)
(* - It is extremely important that active processes only receives M1      *)
(*   messages after sending the M1 message to their neighbour. If this     *)
(*   order is not kept, an active process will become either waiting or    *)
(*   passive and the action ActiveSendM1 will be disabled. This is         *)
(*   equivalent to losing a message, which will make the protocol          *)
(*   misbehave.                                                            *)
(***************************************************************************)
ActiveReceiveM1(p) ==
    \* Receive an M1 type message only if the process is active
    \* and has sent the initial message to the right neighbour.
    /\ state[p] = "active" /\ started[p] = TRUE
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 1
    /\ LET m1 == Head(queue[p])
       IN IF m1.number > max[p] THEN
              /\ max' = [max EXCEPT ![p] = m1.number]
              /\ state' = [state EXCEPT ![p] = "waiting"]
              /\ queue' = [queue EXCEPT ![p] = Tail(@)]
              /\ UNCHANGED <<phase, started, id, terminated>>
          ELSE
              /\ state' = [state EXCEPT ![p] = "passive"] \* become passive
              /\ LET msg == [type |-> 2, number |-> max[p]]
                 IN queue' = [queue EXCEPT ![p] = Tail(@), \* remove message from the queue
                                           ![neighbour(p)] = Append(@, msg)] \* send new message to neighbor
              /\ UNCHANGED <<phase, started, id, max, terminated>>

(***************************************************************************)
(* The waiting process "p" receives an M1 type message, becoming passive.  *)
(* We do not remove the message from queue[p] because according the        *)
(* algorithm, we need to execute the operation in PassiveReceiveM1. By not *)
(* removing the message from the queue we enable PassiveReceiveM1.         *)
(***************************************************************************)
WaitingReceiveM1(p) ==
    /\ state[p] = "waiting"
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 1
    /\ state' = [state EXCEPT ![p] = "passive"]
    /\ UNCHANGED <<phase, started, id, max, queue, terminated>>

(***************************************************************************)
(* The waiting process "p" receives an M2 type message. This signals the   *)
(* beginning of a new phase for p, so it becomes active once again.        *)
(***************************************************************************)
WaitingReceiveM2(p) ==
    /\ state[p] = "waiting"
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 2
    /\ LET m2 == Head(queue[p])
       IN /\ m2.number = max[p]
          /\ phase' = [phase EXCEPT ![p] = @ + 1]     \* increment phase
          /\ state' = [state EXCEPT ![p] = "active"]  \* become active
          /\ started' = [started EXCEPT ![p] = FALSE] \* has not yet started the new phase
          /\ queue' = [queue EXCEPT ![p] = Tail(@)]   \* remove message from the queue
          /\ UNCHANGED <<id, max, terminated>>

(***************************************************************************)
(* The passive process "p" receives an M1 type message "m".                *)
(*                                                                         *)
(* - If m's number is higher or equal to p's maximum and m's counter is    *)
(* higher than 1, then p simply forwards m to it's neighbor, decrementing  *)
(* m's counter.                                                            *)
(*                                                                         *)
(* - If m's number is higher or equal to p's maximum and m's counter is    *)
(* lower or equal to one, then p stops being passive and starts waiting    *)
(* for a message to become active or passive again. p's phase jumps to the *)
(* one contained within m and p forwards the m to it's neighbor, with      *)
(* counter at 0.                                                           *)
(*                                                                         *)
(* - If none of the previous conditions are met, p forwards the m to it's  *)
(* neighbor, with counter at 0.                                            *)
(***************************************************************************)
PassiveReceiveM1(p) ==
    /\ state[p] = "passive"
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 1
    /\ LET m1 == Head(queue[p])
       IN IF m1.number >= max[p] /\ m1.counter >= 1 THEN
              /\ max' = [max EXCEPT ![p] = m1.number]
              /\ IF m1.counter > 1 THEN
                     /\ LET msg == [m1 EXCEPT !.counter = @ - 1] \* create an equal M1 message but with counter - 1
                        IN queue' = [queue EXCEPT ![p] = Tail(@), \* remove message from the queue
                                                  ![neighbour(p)] = Append(@, msg)] \* send new message to neighbour
                     /\ UNCHANGED <<phase, started, state, id, terminated>>
                 ELSE
                     /\ state' = [state EXCEPT ![p] = "waiting"] \* become waiting
                     /\ phase' = [phase EXCEPT ![p] = m1.phase] \* update phase
                     /\ LET msg == [m1 EXCEPT !.counter = 0] \* create an equal M1 message buth with counter = 0
                        IN queue' = [queue EXCEPT ![p] = Tail(@), \* remove message from the queue
                                                  ![neighbour(p)] = Append(@, msg)] \* send new message to neighbour
                     /\ UNCHANGED <<started, id, terminated>>
          ELSE
              /\ LET msg == [m1 EXCEPT !.counter = 0] \* create an equal M1 message buth with counter = 0
                 IN queue' = [queue EXCEPT ![p] = Tail(@), \* remove message from the queue
                                           ![neighbour(p)] = Append(@, msg)] \* send new message to neighbour
              /\ UNCHANGED <<phase, started, id, max, state, terminated>>

(***************************************************************************)
(* The passive process "p" receives a M2 type message "m".                 *)
(*                                                                         *)
(* - If m's number is equal to id[p] then the algorithm terminates,        *)
(*   process p is the leader.                                              *)
(*                                                                         *)
(* - If m's number is lower than p's maximum, then the message is ignored  *)
(*                                                                         *)
(* - If m's number is higher than p's maximum, then p forwards the message *)
(*   to it's neighbour                                                     *)
(***************************************************************************)
PassiveReceiveM2(p) ==
    /\ state[p] = "passive"
    /\ Len(queue[p]) > 0 /\ Head(queue[p]).type = 2
    /\ LET m2 == Head(queue[p])
       IN IF m2.number = id[p] THEN
              /\ terminated' = TRUE \* algorithm terminates, p is the leader
              /\ UNCHANGED <<phase, started, state, id, max, queue>>
          ELSE IF m2.number < max[p] THEN
              \* Ignore message, just remove it from the queue.
              /\ queue' = [queue EXCEPT ![p] = Tail(@)]
              /\ UNCHANGED <<phase, started, state, id, max, terminated>>
          ELSE
              /\ queue' = [queue EXCEPT ![p] = Tail(@), \* remove message from the queue
                                        ![neighbour(p)] = Append(@, m2)] \* forward message to neighbour
              /\ UNCHANGED <<phase, started, state, id, max, terminated>>

--------------------------------------------------------------------------------

(******************************************************************************)
(* Loses a message from queue of process p. Taken from the code of ABP given  *)
(* by the professor.                                                          *)
(******************************************************************************)
Lose(p) ==
    LET
        q == queue[p]
    IN
        /\ q # <<>>
        /\ \E i \in 1..Len(q) : \* removes the ith message from queue[p]
               queue' = [queue EXCEPT ![p] =
                   [j \in 1..(Len(q)-1) |-> IF j < i THEN q[j] ELSE q[j+1]]
               ]
        /\ UNCHANGED<<phase, started, state, id, max, terminated>>

--------------------------------------------------------------------------------

(******************************************************************************)
(* The next action simply states that if we haven't terminated yet, we either *)
(* send an M1 message as an active process or receive a message whatever the  *)
(* state the process is in.                                                   *)
(******************************************************************************)
Next ==
    /\ terminated = FALSE
    /\ \E p \in processes: \/ ActiveSendM1(p)
                           \/ ActiveReceiveM1(p)
                           \/ WaitingReceiveM1(p)
                           \/ WaitingReceiveM2(p)
                           \/ PassiveReceiveM1(p)
                           \/ PassiveReceiveM2(p)

(******************************************************************************)
(* The same as Next but a process can now lose messages.                      *)
(******************************************************************************)
NextLoseMsg ==
    /\ terminated = FALSE
    /\ \E p \in processes: \/ ActiveSendM1(p)
                           \/ ActiveReceiveM1(p)
                           \/ WaitingReceiveM1(p)
                           \/ WaitingReceiveM2(p)
                           \/ PassiveReceiveM1(p)
                           \/ PassiveReceiveM2(p)
                           \/ Lose(p)

--------------------------------------------------------------------------------

(******************************************************************************)
(* The algorithm should finish within a finite time once the leader is        *)
(* selected. We simply say that eventually it's always going to be true that  *)
(* the flag terminated is TRUE.                                               *)
(******************************************************************************)
Termination == <>[](terminated = TRUE)

(******************************************************************************)
(* There is exactly one process that considers itself as leader.              *)
(* This means that eventually it's always going to be true that exists a      *)
(* process l that has it's max equal to it's id and that all the other        *)
(* processes have a max different than their ids. This means that process l   *)
(* is the leader.                                                             *)
(******************************************************************************)
Uniqueness ==
    <>[](\E l \in processes: /\ max[l] = id[l]
                             /\ \A p \in processes \ {l}: max[p] # id[p])

(******************************************************************************)
(* All processes know who the leader is. Eventually it's always true that any *)
(* two processes have the same max.                                           *)
(******************************************************************************)
Agreement ==
    \A p1, p2 \in processes: <>[](max[p1] = max[p2])

--------------------------------------------------------------------------------

Fairness ==
    \A p \in processes: /\ SF_vars(ActiveSendM1(p))
                        /\ WF_vars(ActiveReceiveM1(p))
                        /\ WF_vars(WaitingReceiveM1(p))
                        /\ WF_vars(WaitingReceiveM2(p))
                        /\ WF_vars(PassiveReceiveM1(p))
                        /\ WF_vars(PassiveReceiveM2(p))

(******************************************************************************)
(* Initially Init is satisfied and we will respect Fairness, each step after, *)
(* either a Next action happens or none of the variables change. Use this     *)
(* Spec to run a model without losing messages, all temporal properties       *)
(* should be satisfied.                                                       *)
(******************************************************************************)
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

(******************************************************************************)
(* Initially Init is satisfied and we will respect Fairness, each step after, *)
(* either a NextLoseMsg action happens or none of the variables change. Use   *)
(* this SpecLoseMsg to run a model where processes can lose messages, all     *)
(* temporal properties should be satisfied.                                   *)
(******************************************************************************)
SpecLoseMsg ==
    /\ Init
    /\ [][NextLoseMsg]_vars
    /\ Fairness

================================================================================
