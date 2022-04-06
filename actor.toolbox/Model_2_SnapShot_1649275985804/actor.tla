------------------------------- MODULE actor -------------------------------
EXTENDS TLC, Integers, Sequences

between01(n1, nb, n2) == (nb >= 0) /\ (((n1 < n2) /\ ((n1 < nb) /\ (nb <= n2))) \/ ((n1 >= n2) /\ ((n1 < nb) \/ (nb <= n2))))
between00(n1, nb, n2) == (nb >= 0) /\ (((n1 < n2) /\ ((n1 < nb) /\ (nb < n2))) \/ ((n1 >= n2) /\ ((n1 < nb) \/ (nb < n2))))

fingerStart(myId, k, m) == (myId + (2^(k-1)))%m

CONSTANTS m, bm

(*--fair algorithm ActorStuff {
variables actorInboxes = (0 :>  << <<"FindPredecessor", 6, 0>> >>) @@ (1 :>  <<>>) @@ (3 :> <<>>);
          triggered = FALSE;
          \* make local
          fingerTables =  (0 :> ((1 :> 0) @@ (2 :> 0) @@ (4 :> 0))) 
          @@ (1 :> ((2 :> "no") @@ (3 :> "no") @@ (5 :> "no")))
          @@ (3 :> ((4 :> "no") @@ (5 :> "no") @@ (7 :> "no")));
          predecessors = (0 :> 0) @@ (1 :> 0) @@ (3 :> 0);

fair process (actor \in {0, 1, 3})
variables currentMessage = <<"?", "no9", "no10">>;
  kind = "?";
  id = "no11";
  asker = "no12";
  i;
  joined = FALSE;
  predecessorAnswer = "no13";
  predecessorSuccessorAnswer = "no14";
  k;
  gotPredecessor = "no15";
{
  Join:
    if (self = 0){
        joined := TRUE;
    }else{
        actorInboxes[0] := Append(actorInboxes[0], <<"FindPredecessor", fingerStart(self, 1, bm), self>>);
        await predecessorAnswer # "no13" /\ predecessorSuccessorAnswer # "no14";
        predecessors[self] := predecessorAnswer;
        fingerTables[self][fingerStart(self, 1, bm)] := predecessorSuccessorAnswer;
        joined := TRUE;
    };
  Stabilize:+
    actorInboxes[self] := Append(actorInboxes[self], <<"Stabilize", 1>>);
  WaitForMessages:+
    await joined;
    WhileAfterJoin:
    while (TRUE) {
      print fingerTables;
      print predecessors;
      if (actorInboxes[self] /= <<>>) {
         currentMessage := Head(actorInboxes[self]);
         kind := Head(currentMessage);
         actorInboxes[self] := Tail(actorInboxes[self]);
        };
        {
         T1:
         await kind = "FindPredecessor";
         id := currentMessage[2];
         asker := currentMessage[3];
         await fingerTables[self][fingerStart(self, 1, bm)] # "no";
         if (between01(self, id, fingerTables[self][fingerStart(self, 1, bm)])){
             actorInboxes[asker] := 
             Append(actorInboxes[asker], <<"Predecessor", self,  fingerTables[self][fingerStart(self, 1, bm)]>>);
         } else {
             i := m;
             await fingerTables[self] # "no";
             FindFirstSuitableI:
             while (i > 0 /\ ~(fingerStart(self, i, bm) \in DOMAIN fingerTables[self])){
                i := i - 1;
             };
             await fingerTables[self][fingerStart(self, i, bm)] # "no";
             MainLoop:
             while (i > 0 /\ ~(between00(self, fingerTables[self][fingerStart(self, i, bm)], id))){
                 i := i - 1;
                 FindSuitableI:
                 while (i > 0 /\ ~(fingerStart(self, i, bm) \in DOMAIN fingerTables[self])){
                     i:= i - 1;
                 };
             };
             if (i = 0){
                 actorInboxes[fingerTables[self][fingerStart(self, m, bm)]] := 
                 Append(actorInboxes[fingerTables[self][fingerStart(self, m, bm)]], currentMessage);
             }else{
                 actorInboxes[fingerTables[self][fingerStart(self, i, bm)]] := 
                 Append(actorInboxes[fingerTables[self][fingerStart(self, i, bm)]], currentMessage);
             };
         };
         T2:
            await kind = "Predecessor";
            predecessorAnswer := currentMessage[2];
            predecessorSuccessorAnswer := currentMessage[3];
         T3: 
            await kind = "Stabilize";
            k := currentMessage[2];
            actorInboxes[fingerTables[self][fingerStart(self, k, bm)]] := 
            Append(actorInboxes[fingerTables[self][fingerStart(self, k, bm)]], <<"GetPredecessor", self>>);
            FinishStabilize:
            {
                await gotPredecessor # "no" /\ fingerTables[self][fingerStart(self, 1, bm)] # "no";
                if (between00(gotPredecessor, fingerTables[self][fingerStart(self, 1, bm)], self)){
                    fingerTables[self][fingerStart(self, 1, bm)] := gotPredecessor;
                };
                actorInboxes[fingerTables[self][fingerStart(self, 1, bm)]] := 
                Append(actorInboxes[fingerTables[self][fingerStart(self, 1, bm)]], <<"Notify", self>>);
            };
         T4: 
            await kind = "GetPredecessor";
            actorInboxes[currentMessage[2]] := 
            Append(actorInboxes[currentMessage[2]], <<"GotPredecessor", predecessors[self]>>);
         T5: 
            await kind = "GotPredecessor";
            gotPredecessor := currentMessage[2];
         T6:
            await kind = "Notify";
            if (predecessors[self] # "no"){
                if (between00(currentMessage[2], self, predecessors[self])){
                    predecessors[self] := currentMessage[2];
                };
            }; 
        };
         currentMessage := <<"?", "no", "no">>;
         kind := "?";
         id := "no";
         asker := "no";
    };   
};
};
*)
\* BEGIN TRANSLATION (chksum(pcal) = "5fe598c5" /\ chksum(tla) = "cde1094b")
CONSTANT defaultInitValue
VARIABLES actorInboxes, triggered, fingerTables, predecessors, pc, 
          currentMessage, kind, id, asker, i, joined, predecessorAnswer, 
          predecessorSuccessorAnswer, k, gotPredecessor

vars == << actorInboxes, triggered, fingerTables, predecessors, pc, 
           currentMessage, kind, id, asker, i, joined, predecessorAnswer, 
           predecessorSuccessorAnswer, k, gotPredecessor >>

ProcSet == ({0, 1, 3})

Init == (* Global variables *)
        /\ actorInboxes = (0 :>  << <<"FindPredecessor", 6, 0>> >>) @@ (1 :>  <<>>) @@ (3 :> <<>>)
        /\ triggered = FALSE
        /\ fingerTables =                 (0 :> ((1 :> 0) @@ (2 :> 0) @@ (4 :> 0)))
                          @@ (1 :> ((2 :> "no") @@ (3 :> "no") @@ (5 :> "no")))
                          @@ (3 :> ((4 :> "no") @@ (5 :> "no") @@ (7 :> "no")))
        /\ predecessors = (0 :> 0) @@ (1 :> 0) @@ (3 :> 0)
        (* Process actor *)
        /\ currentMessage = [self \in {0, 1, 3} |-> <<"?", "no9", "no10">>]
        /\ kind = [self \in {0, 1, 3} |-> "?"]
        /\ id = [self \in {0, 1, 3} |-> "no11"]
        /\ asker = [self \in {0, 1, 3} |-> "no12"]
        /\ i = [self \in {0, 1, 3} |-> defaultInitValue]
        /\ joined = [self \in {0, 1, 3} |-> FALSE]
        /\ predecessorAnswer = [self \in {0, 1, 3} |-> "no13"]
        /\ predecessorSuccessorAnswer = [self \in {0, 1, 3} |-> "no14"]
        /\ k = [self \in {0, 1, 3} |-> defaultInitValue]
        /\ gotPredecessor = [self \in {0, 1, 3} |-> "no15"]
        /\ pc = [self \in ProcSet |-> "Join"]

Join(self) == /\ pc[self] = "Join"
              /\ IF self = 0
                    THEN /\ joined' = [joined EXCEPT ![self] = TRUE]
                         /\ UNCHANGED << actorInboxes, fingerTables, 
                                         predecessors >>
                    ELSE /\ actorInboxes' = [actorInboxes EXCEPT ![0] = Append(actorInboxes[0], <<"FindPredecessor", fingerStart(self, 1, bm), self>>)]
                         /\ predecessorAnswer[self] # "no13" /\ predecessorSuccessorAnswer[self] # "no14"
                         /\ predecessors' = [predecessors EXCEPT ![self] = predecessorAnswer[self]]
                         /\ fingerTables' = [fingerTables EXCEPT ![self][fingerStart(self, 1, bm)] = predecessorSuccessorAnswer[self]]
                         /\ joined' = [joined EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "Stabilize"]
              /\ UNCHANGED << triggered, currentMessage, kind, id, asker, i, 
                              predecessorAnswer, predecessorSuccessorAnswer, k, 
                              gotPredecessor >>

Stabilize(self) == /\ pc[self] = "Stabilize"
                   /\ actorInboxes' = [actorInboxes EXCEPT ![self] = Append(actorInboxes[self], <<"Stabilize", 1>>)]
                   /\ pc' = [pc EXCEPT ![self] = "WaitForMessages"]
                   /\ UNCHANGED << triggered, fingerTables, predecessors, 
                                   currentMessage, kind, id, asker, i, joined, 
                                   predecessorAnswer, 
                                   predecessorSuccessorAnswer, k, 
                                   gotPredecessor >>

WaitForMessages(self) == /\ pc[self] = "WaitForMessages"
                         /\ joined[self]
                         /\ pc' = [pc EXCEPT ![self] = "WhileAfterJoin"]
                         /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                                         predecessors, currentMessage, kind, 
                                         id, asker, i, joined, 
                                         predecessorAnswer, 
                                         predecessorSuccessorAnswer, k, 
                                         gotPredecessor >>

WhileAfterJoin(self) == /\ pc[self] = "WhileAfterJoin"
                        /\ PrintT(fingerTables)
                        /\ PrintT(predecessors)
                        /\ IF actorInboxes[self] /= <<>>
                              THEN /\ currentMessage' = [currentMessage EXCEPT ![self] = Head(actorInboxes[self])]
                                   /\ kind' = [kind EXCEPT ![self] = Head(currentMessage'[self])]
                                   /\ actorInboxes' = [actorInboxes EXCEPT ![self] = Tail(actorInboxes[self])]
                              ELSE /\ TRUE
                                   /\ UNCHANGED << actorInboxes, 
                                                   currentMessage, kind >>
                        /\ pc' = [pc EXCEPT ![self] = "T1"]
                        /\ UNCHANGED << triggered, fingerTables, predecessors, 
                                        id, asker, i, joined, 
                                        predecessorAnswer, 
                                        predecessorSuccessorAnswer, k, 
                                        gotPredecessor >>

T1(self) == /\ pc[self] = "T1"
            /\ kind[self] = "FindPredecessor"
            /\ id' = [id EXCEPT ![self] = currentMessage[self][2]]
            /\ asker' = [asker EXCEPT ![self] = currentMessage[self][3]]
            /\ fingerTables[self][fingerStart(self, 1, bm)] # "no"
            /\ IF between01(self, id'[self], fingerTables[self][fingerStart(self, 1, bm)])
                  THEN /\ actorInboxes' = [actorInboxes EXCEPT ![asker'[self]] = Append(actorInboxes[asker'[self]], <<"Predecessor", self,  fingerTables[self][fingerStart(self, 1, bm)]>>)]
                       /\ pc' = [pc EXCEPT ![self] = "T2"]
                       /\ i' = i
                  ELSE /\ i' = [i EXCEPT ![self] = m]
                       /\ fingerTables[self] # "no"
                       /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                       /\ UNCHANGED actorInboxes
            /\ UNCHANGED << triggered, fingerTables, predecessors, 
                            currentMessage, kind, joined, predecessorAnswer, 
                            predecessorSuccessorAnswer, k, gotPredecessor >>

FindFirstSuitableI(self) == /\ pc[self] = "FindFirstSuitableI"
                            /\ IF i[self] > 0 /\ ~(fingerStart(self, i[self], bm) \in DOMAIN fingerTables[self])
                                  THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                                       /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                                  ELSE /\ fingerTables[self][fingerStart(self, i[self], bm)] # "no"
                                       /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                       /\ i' = i
                            /\ UNCHANGED << actorInboxes, triggered, 
                                            fingerTables, predecessors, 
                                            currentMessage, kind, id, asker, 
                                            joined, predecessorAnswer, 
                                            predecessorSuccessorAnswer, k, 
                                            gotPredecessor >>

MainLoop(self) == /\ pc[self] = "MainLoop"
                  /\ IF i[self] > 0 /\ ~(between00(self, fingerTables[self][fingerStart(self, i[self], bm)], id[self]))
                        THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                             /\ pc' = [pc EXCEPT ![self] = "FindSuitableI"]
                             /\ UNCHANGED actorInboxes
                        ELSE /\ IF i[self] = 0
                                   THEN /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables[self][fingerStart(self, m, bm)]] = Append(actorInboxes[fingerTables[self][fingerStart(self, m, bm)]], currentMessage[self])]
                                   ELSE /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables[self][fingerStart(self, i[self], bm)]] = Append(actorInboxes[fingerTables[self][fingerStart(self, i[self], bm)]], currentMessage[self])]
                             /\ pc' = [pc EXCEPT ![self] = "T2"]
                             /\ i' = i
                  /\ UNCHANGED << triggered, fingerTables, predecessors, 
                                  currentMessage, kind, id, asker, joined, 
                                  predecessorAnswer, 
                                  predecessorSuccessorAnswer, k, 
                                  gotPredecessor >>

FindSuitableI(self) == /\ pc[self] = "FindSuitableI"
                       /\ IF i[self] > 0 /\ ~(fingerStart(self, i[self], bm) \in DOMAIN fingerTables[self])
                             THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                                  /\ pc' = [pc EXCEPT ![self] = "FindSuitableI"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                  /\ i' = i
                       /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                                       predecessors, currentMessage, kind, id, 
                                       asker, joined, predecessorAnswer, 
                                       predecessorSuccessorAnswer, k, 
                                       gotPredecessor >>

T2(self) == /\ pc[self] = "T2"
            /\ kind[self] = "Predecessor"
            /\ predecessorAnswer' = [predecessorAnswer EXCEPT ![self] = currentMessage[self][2]]
            /\ predecessorSuccessorAnswer' = [predecessorSuccessorAnswer EXCEPT ![self] = currentMessage[self][3]]
            /\ pc' = [pc EXCEPT ![self] = "T3"]
            /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                            predecessors, currentMessage, kind, id, asker, i, 
                            joined, k, gotPredecessor >>

T3(self) == /\ pc[self] = "T3"
            /\ kind[self] = "Stabilize"
            /\ k' = [k EXCEPT ![self] = currentMessage[self][2]]
            /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables[self][fingerStart(self, k'[self], bm)]] = Append(actorInboxes[fingerTables[self][fingerStart(self, k'[self], bm)]], <<"GetPredecessor", self>>)]
            /\ pc' = [pc EXCEPT ![self] = "FinishStabilize"]
            /\ UNCHANGED << triggered, fingerTables, predecessors, 
                            currentMessage, kind, id, asker, i, joined, 
                            predecessorAnswer, predecessorSuccessorAnswer, 
                            gotPredecessor >>

FinishStabilize(self) == /\ pc[self] = "FinishStabilize"
                         /\ gotPredecessor[self] # "no" /\ fingerTables[self][fingerStart(self, 1, bm)] # "no"
                         /\ IF between00(gotPredecessor[self], fingerTables[self][fingerStart(self, 1, bm)], self)
                               THEN /\ fingerTables' = [fingerTables EXCEPT ![self][fingerStart(self, 1, bm)] = gotPredecessor[self]]
                               ELSE /\ TRUE
                                    /\ UNCHANGED fingerTables
                         /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables'[self][fingerStart(self, 1, bm)]] = Append(actorInboxes[fingerTables'[self][fingerStart(self, 1, bm)]], <<"Notify", self>>)]
                         /\ pc' = [pc EXCEPT ![self] = "T4"]
                         /\ UNCHANGED << triggered, predecessors, 
                                         currentMessage, kind, id, asker, i, 
                                         joined, predecessorAnswer, 
                                         predecessorSuccessorAnswer, k, 
                                         gotPredecessor >>

T4(self) == /\ pc[self] = "T4"
            /\ kind[self] = "GetPredecessor"
            /\ actorInboxes' = [actorInboxes EXCEPT ![currentMessage[self][2]] = Append(actorInboxes[currentMessage[self][2]], <<"GotPredecessor", predecessors[self]>>)]
            /\ pc' = [pc EXCEPT ![self] = "T5"]
            /\ UNCHANGED << triggered, fingerTables, predecessors, 
                            currentMessage, kind, id, asker, i, joined, 
                            predecessorAnswer, predecessorSuccessorAnswer, k, 
                            gotPredecessor >>

T5(self) == /\ pc[self] = "T5"
            /\ kind[self] = "GotPredecessor"
            /\ gotPredecessor' = [gotPredecessor EXCEPT ![self] = currentMessage[self][2]]
            /\ pc' = [pc EXCEPT ![self] = "T6"]
            /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                            predecessors, currentMessage, kind, id, asker, i, 
                            joined, predecessorAnswer, 
                            predecessorSuccessorAnswer, k >>

T6(self) == /\ pc[self] = "T6"
            /\ kind[self] = "Notify"
            /\ IF predecessors[self] # "no"
                  THEN /\ IF between00(currentMessage[self][2], self, predecessors[self])
                             THEN /\ predecessors' = [predecessors EXCEPT ![self] = currentMessage[self][2]]
                             ELSE /\ TRUE
                                  /\ UNCHANGED predecessors
                  ELSE /\ TRUE
                       /\ UNCHANGED predecessors
            /\ currentMessage' = [currentMessage EXCEPT ![self] = <<"?", "no", "no">>]
            /\ kind' = [kind EXCEPT ![self] = "?"]
            /\ id' = [id EXCEPT ![self] = "no"]
            /\ asker' = [asker EXCEPT ![self] = "no"]
            /\ pc' = [pc EXCEPT ![self] = "WhileAfterJoin"]
            /\ UNCHANGED << actorInboxes, triggered, fingerTables, i, joined, 
                            predecessorAnswer, predecessorSuccessorAnswer, k, 
                            gotPredecessor >>

actor(self) == Join(self) \/ Stabilize(self) \/ WaitForMessages(self)
                  \/ WhileAfterJoin(self) \/ T1(self)
                  \/ FindFirstSuitableI(self) \/ MainLoop(self)
                  \/ FindSuitableI(self) \/ T2(self) \/ T3(self)
                  \/ FinishStabilize(self) \/ T4(self) \/ T5(self)
                  \/ T6(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {0, 1, 3}: actor(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in {0, 1, 3} : /\ WF_vars(actor(self))
                                   /\ SF_vars(Stabilize(self)) /\ SF_vars(WaitForMessages(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Triggered == predecessors = (0 :> 0) @@ (1 :> 0) @@ (3 :> 0)

Liveness == <>[]Triggered

LenStateConstraint == Len(actorInboxes[0])<=1 /\ Len(actorInboxes[1])<=1 /\ Len(actorInboxes[3])<=1

=============================================================================
\* Modification History
\* Last modified Thu Apr 07 01:13:00 YEKT 2022 by pervu
\* Created Sun Jan 30 18:34:11 YEKT 2022 by pervu
