---- MODULE LeaderElectionCrash ----
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS 
    N, \* Number of processes
    F, \* F: number of faulty processes
    STOP \* Max number of rounds for finite search space
ASSUME N \in Nat /\ F <= N /\ F <= STOP
Processes == 1..N

(* --algorithm LeaderElectionCrash 
{

    variable
        f = F,                            \* number of processes left to be crashed
        alive = [p \in Processes |-> TRUE]; \* all processes are initially alive
        mailbox = [p \in Processes |-> {}]; (*** TODO: Initialise all processes with an empty mailbox***)
        leader = [p \in Processes |-> 0];  \* all have not elected any leader
        round = [p \in Processes |-> 0];    \* all are at round 0
        elected = [p \in Processes |-> FALSE];

    define {
        Max(S) == CHOOSE max \in S: \A y \in S: max >= y (*** TODO: Pick the highest value in S ***)
    }

    macro MaybeCrash() {
    if (f>0 /\ alive[self] /\ STOP-round[self] > 1) { \* Disallow crashing just before STOP
            either {
                (*** TODO: process crashes... ***)
                alive[self] := FALSE;
                f := f - 1;
            } 
            or skip; }; \* ... or not
    }
    
    fair process (p \in Processes)
    variable recv={};
    {
P:   while (round[self] < STOP) {
        recv := Processes;
Bcast:  while (alive[self] /\ recv # {}) {
            with (p \in recv) {
                (*** TODO: Send 'self' to all processes ***)
                mailbox[p] := mailbox[p] \union {self};
                recv := recv \ {p};
                MaybeCrash();
            };
        };  
        (*** TODO: Advance to the next round ***)
        round[self] := round[self] + 1;
        elected := [p \in Processes |-> FALSE];
Sync:   (*** TODO: Wait for processes to be in next round ***)
        if (alive[self]){
            await \A pid \in Processes: alive[pid] => round[pid] >= round[self];
            mailbox[self] := {x \in mailbox[self]:  alive[x] = TRUE};
            leader[self] := Max(mailbox[self]);(*** TODO: Choose leader ***)
            elected[self] := TRUE;
            await \A pid \in Processes: elected[pid] = TRUE;
                \* mailbox[self] := {};
        }

    };
END: skip;
    } \* end process

}

*)
\* BEGIN TRANSLATION (chksum(pcal) = "f93d379a" /\ chksum(tla) = "2b818c2e")
VARIABLES f, alive, mailbox, leader, round, elected, pc

(* define statement *)
Max(S) == CHOOSE max \in S: \A y \in S: max >= y

VARIABLE recv

vars == << f, alive, mailbox, leader, round, elected, pc, recv >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ f = F
        /\ alive = [p \in Processes |-> TRUE]
        /\ mailbox = [p \in Processes |-> {}]
        /\ leader = [p \in Processes |-> 0]
        /\ round = [p \in Processes |-> 0]
        /\ elected = [p \in Processes |-> FALSE]
        (* Process p *)
        /\ recv = [self \in Processes |-> {}]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF round[self] < STOP
                 THEN /\ recv' = [recv EXCEPT ![self] = Processes]
                      /\ pc' = [pc EXCEPT ![self] = "Bcast"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "END"]
                      /\ recv' = recv
           /\ UNCHANGED << f, alive, mailbox, leader, round, elected >>

Bcast(self) == /\ pc[self] = "Bcast"
               /\ IF alive[self] /\ recv[self] # {}
                     THEN /\ \E p \in recv[self]:
                               /\ mailbox' = [mailbox EXCEPT ![p] = mailbox[p] \union {self}]
                               /\ recv' = [recv EXCEPT ![self] = recv[self] \ {p}]
                               /\ IF f>0 /\ alive[self] /\ STOP-round[self] > 1
                                     THEN /\ \/ /\ alive' = [alive EXCEPT ![self] = FALSE]
                                                /\ f' = f - 1
                                             \/ /\ TRUE
                                                /\ UNCHANGED <<f, alive>>
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << f, alive >>
                          /\ pc' = [pc EXCEPT ![self] = "Bcast"]
                          /\ UNCHANGED << round, elected >>
                     ELSE /\ round' = [round EXCEPT ![self] = round[self] + 1]
                          /\ elected' = [p \in Processes |-> FALSE]
                          /\ pc' = [pc EXCEPT ![self] = "Sync"]
                          /\ UNCHANGED << f, alive, mailbox, recv >>
               /\ UNCHANGED leader

Sync(self) == /\ pc[self] = "Sync"
              /\ IF alive[self]
                    THEN /\ \A pid \in Processes: alive[pid] => round[pid] >= round[self]
                         /\ mailbox' = [mailbox EXCEPT ![self] = {x \in mailbox[self]:  alive[x] = TRUE}]
                         /\ leader' = [leader EXCEPT ![self] = Max(mailbox'[self])]
                         /\ elected' = [elected EXCEPT ![self] = TRUE]
                         /\ \A pid \in Processes: elected'[pid] = TRUE
                    ELSE /\ TRUE
                         /\ UNCHANGED << mailbox, leader, elected >>
              /\ pc' = [pc EXCEPT ![self] = "P"]
              /\ UNCHANGED << f, alive, round, recv >>

END(self) == /\ pc[self] = "END"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << f, alive, mailbox, leader, round, elected, recv >>

p(self) == P(self) \/ Bcast(self) \/ Sync(self) \/ END(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Processes: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Processes : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Completeness == <>(\A m \in Processes: leader[m] # 0 /\ alive[m]  => (alive[leader[m]] = TRUE))
Agreement == (\A m, n \in Processes: (alive[m] /\ alive[n]) /\ (elected[m] /\ elected[n])=> leader[m] = leader[n])



====
