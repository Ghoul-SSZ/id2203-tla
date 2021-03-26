------------------------------- MODULE Paxos -------------------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANT M, N, STOP, MAXB
ASSUME M \in Nat /\ N \in Nat /\ M<=N
Proposer == 0..M-1
Acceptor == M..N
\* \* M Proposers, and N-M+1 acceptors
Slots == 1..STOP
Ballots == 0..MAXB
\* \* In the model, use M=2, N=3, STOP=2 (number of slots), MAXB=2

(*--algorithm Paxos
 { variable AccMsg={}, PMsg={}, len=0, majority=((N-M+1)+1) \div 2; \* AccMsg: all Acceptor's receiving channel and PMsg: All Proposers' recv channel 

   define{
   ExtractValSet(S) == {m.valSet : m \in S} 
   MaxVal(S,s) == IF \E tuple \in S: tuple[1] = s
                  THEN CHOOSE e \in S: \A y \in S: y[2] <= e[2](*** TODO: Pick the tuple <<s,b,v>> from S that has the given slot s and highest ballot b ***)
                  ELSE {}
   ExistMsg(C, t, b) == \E m \in C: m.type=t /\ m.bal = b (*** Checks if there exists a msg with type t and ballot b in C ***)

   SentAccMsgs(t,b) == IF ExistMsg(AccMsg, t, b)
                       THEN {msg \in AccMsg: msg.type=t /\ msg.bal=b}
                       ELSE {}
   (*** TODO: Get all the msgs in AccMsg that has type t and ballot b***)
   SentPMsgs(t,b) == IF ExistMsg(PMsg, t, b)
                     THEN {msg \in PMsg: msg.type=t /\ msg.bal=b}(*** TODO: Same as above but with PMsg***)
                     ELSE {}
   SentPMsgs2(t,b,s) == IF ExistMsg(PMsg, t, b)
                        THEN {msg \in PMsg: msg.type=t /\ msg.bal=b /\ msg.slot=s}
                        ELSE {}
                     (*** TODO: Same as above but match slot s as well ***)
   
   LostLeadership(b) == Cardinality({m \in PMsg: m.bal > b}) >= majority (*** Check if leadership with the ballot b has been lost***) 
   }
   
\* \* Proposer calls this to send prepare msg to acceptors
   macro SendPrepare (b) 
   {
     AccMsg:=AccMsg \union {[type |->"prepare", bal |-> b]};
   }

\* \* acceptor calls this to reply with a promise msg to Proposer
   macro ReplyPrepare (b)
   {
    await (b> maxBal) /\ ExistMsg(AccMsg, "prepare",b);
    maxBal:=b;
    (*** TODO: Send Promise of this ballot ***)
    PMsg := PMsg \union {[type |-> "promise", bal |-> maxBal, valSet |-> acceptedValues]};
   }

\* \* Proposer calls this to collect promise msgs from acceptors
   macro CollectPromises (b) 
   {
    await Cardinality(SentPMsgs("promise", b)) >= majority(*** TODO: Wait for either getting a majority of promises from acceptors ***) 
          \/ LostLeadership(b);    (*** OR we lost leadership i.e. another proposer has overtaken us as leader ***)
    if (~ LostLeadership(b)) {
       elected:=TRUE;
       pVal:=UNION ExtractValSet(SentPMsgs("promise",b));
    }  
   }


\* \* Proposer calls this to send accept msg to acceptors
   macro SendAccept (b,s) 
   {
    if (Cardinality({pv \in pVal: pv[1]=s})=0)
         AccMsg:=AccMsg \union {[type |-> "accept", bal |-> b, slot |-> s, val |-> <<s,b,self>> ]};
    else AccMsg:=AccMsg \union {[type |-> "accept", bal |-> b, slot |-> s, val |->MaxVal(pVal,s)]};  
   }

\* \* acceptor calls this to reply with a accepted msg to Proposer
   macro ReplyAccept (b) 
   {
    await (b>= maxBal); 
    with (m \in SentAccMsgs("accept",b)){
      maxBal:=b; 
      acceptedValues:= acceptedValues \union {m.val}; \* update val heard with message of maxBal so far
      PMsg:=PMsg \union {[type |->"accepted", acc |-> self, bal |-> b, slot|-> m.slot, vv |->m.val[3] ]};
    }
   }

\* \* Proposer calls this to collect promise msgs from acceptors
   macro CollectAccepted (b,s) 
   {
    await \/ Cardinality(SentPMsgs2("accepted", b, s)) >= majority (*** TODO: Wait for either getting a majority of accepted from acceptors ***) 
          \/ LostLeadership(b);    (*** OR we lost leadership i.e. another proposer has overtaken us as leader ***)
    if (LostLeadership(b)) {
       elected:=FALSE;
    }
    else with (m \in SentPMsgs("accepted",b)) {lv:=m.vv;}   
   }

\* \* Proposer calls this to finalize decision for slot s
   macro SendDecide (b,s) 
   {
    AccMsg := AccMsg \union {[type |-> "decide", bal |-> b, slot |-> s, dcd |->lv ]};
   }

\* \* acceptor calls this to finalize decision for slot 
   macro RcvDecide (b) 
   {
    await (b>= maxBal); 
    with (m \in SentAccMsgs("decide",b)){
      maxBal:=b;
      decided[m.slot]:= decided[m.slot] \union {m.dcd};
    }
   }
   
\* \* Acceptor process actions
   fair process (a \in Acceptor)
   variable maxBal=-1, acceptedValues={<<-1,-1,-1>>}, \* \* <<s,b,v>>
            decided=[i \in Slots |-> {}];
   {
    A:  while (TRUE) {
            with (ba \in Ballots) {
                either ReplyPrepare(ba)
                or ReplyAccept(ba)
                or RcvDecide(ba)
            }
        }
   } 


\* \* Proposer process
   fair process (p \in Proposer)
   variable b=self, s=1, elected=FALSE, lv=-1, pVal={<<-1,-1,-1>>}; \* \* <<s,b,v>> 
   {
    L:  while (s \in Slots /\ b \in Ballots) {
        \*\* Try to get elected as Leader first
        P1L:  while (elected # TRUE) { 
                b:=b+M; \*\* guarantees unique ballot num
                if (b > MAXB) {
                    goto END;
                } else {
                    SendPrepare(b);
        CP1L:       CollectPromises(b);
                }
        }; 
        \*\* Move to phase2          
        P2L:  SendAccept(b,s);
        CP2L: CollectAccepted(b,s); 
        \*\* Move to phase 3      
        P3L:  if (elected=TRUE){ \*\* Proposer may have been overtaken in CP2L
                SendDecide (b,s); 
                s:=s+1;
              };
        };
   END: skip;   
   } 

}
*)
\* BEGIN TRANSLATION (chksum(pcal) = "2d690360" /\ chksum(tla) = "c1b2e4b5")
VARIABLES AccMsg, PMsg, len, majority, pc

(* define statement *)
ExtractValSet(S) == {m.valSet : m \in S}
MaxVal(S,s) == IF \E tuple \in S: tuple[1] = s
               THEN CHOOSE e \in S: \A y \in S: y[2] <= e[2]
               ELSE {}
ExistMsg(C, t, b) == \E m \in C: m.type=t /\ m.bal = b

SentAccMsgs(t,b) == IF ExistMsg(AccMsg, t, b)
                    THEN {msg \in AccMsg: msg.type=t /\ msg.bal=b}
                    ELSE {}

SentPMsgs(t,b) == IF ExistMsg(PMsg, t, b)
                  THEN {msg \in PMsg: msg.type=t /\ msg.bal=b}
                  ELSE {}
SentPMsgs2(t,b,s) == IF ExistMsg(PMsg, t, b)
                     THEN {msg \in PMsg: msg.type=t /\ msg.bal=b /\ msg.slot=s}
                     ELSE {}


LostLeadership(b) == Cardinality({m \in PMsg: m.bal > b}) >= majority

VARIABLES maxBal, acceptedValues, decided, b, s, elected, lv, pVal

vars == << AccMsg, PMsg, len, majority, pc, maxBal, acceptedValues, decided, 
           b, s, elected, lv, pVal >>

ProcSet == (Acceptor) \cup (Proposer)

Init == (* Global variables *)
        /\ AccMsg = {}
        /\ PMsg = {}
        /\ len = 0
        /\ majority = (((N-M+1)+1) \div 2)
        (* Process a *)
        /\ maxBal = [self \in Acceptor |-> -1]
        /\ acceptedValues = [self \in Acceptor |-> {<<-1,-1,-1>>}]
        /\ decided = [self \in Acceptor |-> [i \in Slots |-> {}]]
        (* Process p *)
        /\ b = [self \in Proposer |-> self]
        /\ s = [self \in Proposer |-> 1]
        /\ elected = [self \in Proposer |-> FALSE]
        /\ lv = [self \in Proposer |-> -1]
        /\ pVal = [self \in Proposer |-> {<<-1,-1,-1>>}]
        /\ pc = [self \in ProcSet |-> CASE self \in Acceptor -> "A"
                                        [] self \in Proposer -> "L"]

A(self) == /\ pc[self] = "A"
           /\ \E ba \in Ballots:
                \/ /\ (ba> maxBal[self]) /\ ExistMsg(AccMsg, "prepare",ba)
                   /\ maxBal' = [maxBal EXCEPT ![self] = ba]
                   /\ PMsg' = (PMsg \union {[type |-> "promise", bal |-> maxBal'[self], valSet |-> acceptedValues[self]]})
                   /\ UNCHANGED <<acceptedValues, decided>>
                \/ /\ (ba>= maxBal[self])
                   /\ \E m \in SentAccMsgs("accept",ba):
                        /\ maxBal' = [maxBal EXCEPT ![self] = ba]
                        /\ acceptedValues' = [acceptedValues EXCEPT ![self] = acceptedValues[self] \union {m.val}]
                        /\ PMsg' = (PMsg \union {[type |->"accepted", acc |-> self, bal |-> ba, slot|-> m.slot, vv |->m.val[3] ]})
                   /\ UNCHANGED decided
                \/ /\ (ba>= maxBal[self])
                   /\ \E m \in SentAccMsgs("decide",ba):
                        /\ maxBal' = [maxBal EXCEPT ![self] = ba]
                        /\ decided' = [decided EXCEPT ![self][m.slot] = decided[self][m.slot] \union {m.dcd}]
                   /\ UNCHANGED <<PMsg, acceptedValues>>
           /\ pc' = [pc EXCEPT ![self] = "A"]
           /\ UNCHANGED << AccMsg, len, majority, b, s, elected, lv, pVal >>

a(self) == A(self)

L(self) == /\ pc[self] = "L"
           /\ IF s[self] \in Slots /\ b[self] \in Ballots
                 THEN /\ pc' = [pc EXCEPT ![self] = "P1L"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "END"]
           /\ UNCHANGED << AccMsg, PMsg, len, majority, maxBal, acceptedValues, 
                           decided, b, s, elected, lv, pVal >>

P1L(self) == /\ pc[self] = "P1L"
             /\ IF elected[self] # TRUE
                   THEN /\ b' = [b EXCEPT ![self] = b[self]+M]
                        /\ IF b'[self] > MAXB
                              THEN /\ pc' = [pc EXCEPT ![self] = "END"]
                                   /\ UNCHANGED AccMsg
                              ELSE /\ AccMsg' = (AccMsg \union {[type |->"prepare", bal |-> b'[self]]})
                                   /\ pc' = [pc EXCEPT ![self] = "CP1L"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "P2L"]
                        /\ UNCHANGED << AccMsg, b >>
             /\ UNCHANGED << PMsg, len, majority, maxBal, acceptedValues, 
                             decided, s, elected, lv, pVal >>

CP1L(self) == /\ pc[self] = "CP1L"
              /\ Cardinality(SentPMsgs("promise", b[self])) >= majority
                 \/ LostLeadership(b[self])
              /\ IF ~ LostLeadership(b[self])
                    THEN /\ elected' = [elected EXCEPT ![self] = TRUE]
                         /\ pVal' = [pVal EXCEPT ![self] = UNION ExtractValSet(SentPMsgs("promise",b[self]))]
                    ELSE /\ TRUE
                         /\ UNCHANGED << elected, pVal >>
              /\ pc' = [pc EXCEPT ![self] = "P1L"]
              /\ UNCHANGED << AccMsg, PMsg, len, majority, maxBal, 
                              acceptedValues, decided, b, s, lv >>

P2L(self) == /\ pc[self] = "P2L"
             /\ IF Cardinality({pv \in pVal[self]: pv[1]=s[self]})=0
                   THEN /\ AccMsg' = (AccMsg \union {[type |-> "accept", bal |-> b[self], slot |-> s[self], val |-> <<s[self],b[self],self>> ]})
                   ELSE /\ AccMsg' = (AccMsg \union {[type |-> "accept", bal |-> b[self], slot |-> s[self], val |->MaxVal(pVal[self],s[self])]})
             /\ pc' = [pc EXCEPT ![self] = "CP2L"]
             /\ UNCHANGED << PMsg, len, majority, maxBal, acceptedValues, 
                             decided, b, s, elected, lv, pVal >>

CP2L(self) == /\ pc[self] = "CP2L"
              /\ \/ Cardinality(SentPMsgs2("accepted", b[self], s[self])) >= majority
                 \/ LostLeadership(b[self])
              /\ IF LostLeadership(b[self])
                    THEN /\ elected' = [elected EXCEPT ![self] = FALSE]
                         /\ lv' = lv
                    ELSE /\ \E m \in SentPMsgs("accepted",b[self]):
                              lv' = [lv EXCEPT ![self] = m.vv]
                         /\ UNCHANGED elected
              /\ pc' = [pc EXCEPT ![self] = "P3L"]
              /\ UNCHANGED << AccMsg, PMsg, len, majority, maxBal, 
                              acceptedValues, decided, b, s, pVal >>

P3L(self) == /\ pc[self] = "P3L"
             /\ IF elected[self]=TRUE
                   THEN /\ AccMsg' = (AccMsg \union {[type |-> "decide", bal |-> b[self], slot |-> s[self], dcd |->lv[self] ]})
                        /\ s' = [s EXCEPT ![self] = s[self]+1]
                   ELSE /\ TRUE
                        /\ UNCHANGED << AccMsg, s >>
             /\ pc' = [pc EXCEPT ![self] = "L"]
             /\ UNCHANGED << PMsg, len, majority, maxBal, acceptedValues, 
                             decided, b, elected, lv, pVal >>

END(self) == /\ pc[self] = "END"
             /\ TRUE
             /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << AccMsg, PMsg, len, majority, maxBal, 
                             acceptedValues, decided, b, s, elected, lv, pVal >>

p(self) == L(self) \/ P1L(self) \/ CP1L(self) \/ P2L(self) \/ CP2L(self)
              \/ P3L(self) \/ END(self)

Next == (\E self \in Acceptor: a(self))
           \/ (\E self \in Proposer: p(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Acceptor : WF_vars(a(self))
        /\ \A self \in Proposer : WF_vars(p(self))

\* END TRANSLATION 
Validity == \A m \in AccMsg: m.type = "decide" => \E msg \in AccMsg: msg.type = "accept" /\ m.slot = msg.slot /\ m.dcd = msg.val[3]
\* Only proposed values may be decided
UniformAgreement == \A acc1, acc2 \in Acceptor:\A i \in Slots: (decided[acc1][i] # {} /\ decided[acc2][i] # {}) => decided[acc1][i] = decided[acc2][i]
\* No two processes decide different values
Integrity == \A acc1, acc2 \in Acceptor:\A i \in Slots: (decided[acc1][i] # {} /\ decided[acc2][i] # {}) => Cardinality(decided[acc1][i]) = 1 /\ Cardinality(decided[acc2][i]) = 1\* if decided value is not {}, then 
\* Each processes can decide a value at most once
Termination == <>[]\A acc \in Acceptor:\A i \in Slots:  decided[acc][i] # {}
\* Every process eventually decides a value
====
