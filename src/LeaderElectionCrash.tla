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
        mailbox = (*** TODO: Initialise all processes with an empty mailbox***)
        leader = [p \in Processes |-> 0];  \* all have not elected any leader
        round = [p \in Processes |-> 0];    \* all are at round 0

    define {
        Max(S) == (*** TODO: Pick the highest value in S ***)
    }

    macro MaybeCrash() {
    if (f>0 /\ alive[self] /\ STOP-round[self] > 1) { \* Disallow crashing just before STOP
            either { 
                (*** TODO: process crashes... ***)
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
                MaybeCrash();
            };
        };  
        (*** TODO: Advance to the next round ***)
Sync:   (*** TODO: Wait for processes to be in next round ***)
        leader[self] := (*** TODO: Choose leader ***);
    };
    } \* end process

}

*)

====
