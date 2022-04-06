------------------------------- MODULE actor -------------------------------
EXTENDS TLC, Integers, Sequences

between01(n1, nb, n2) == (nb >= 0) /\ (((n1 < n2) /\ ((n1 < nb) /\ (nb <= n2))) \/ ((n1 >= n2) /\ ((n1 < nb) \/ (nb <= n2))))
between00(n1, nb, n2) == (nb >= 0) /\ (((n1 < n2) /\ ((n1 < nb) /\ (nb < n2))) \/ ((n1 >= n2) /\ ((n1 < nb) \/ (nb < n2))))

fingerStart(myId, k, m) == (myId + (2^(k-1)))%m

CONSTANTS m, bm, NULL

(*--fair algorithm ActorStuff {
variables actorInboxes = (0 :>  << <<"FindPredecessor", 6, 0>> >>) @@ (1 :>  <<>>) @@ (3 :> <<>>);
          triggered = FALSE;
          \* make local
          fingerTables =  (0 :> ((1 :> 0) @@ (2 :> 0) @@ (4 :> 0))) 
          @@ (1 :> ((2 :> NULL) @@ (3 :> NULL) @@ (5 :> NULL)))
          @@ (3 :> ((4 :> NULL) @@ (5 :> NULL) @@ (7 :> NULL)));
          predecessors = (0 :> 0) @@ (1 :> NULL) @@ (3 :> NULL);

fair process (actor \in {0, 1, 3})
variables currentMessage = <<"?", NULL, NULL>>;
  kind = "?";
  id = NULL;
  asker = NULL;
  i;
  k;
  joined = FALSE;
  predecessorAnswer = NULL;
  predecessorSuccessorAnswer = NULL;
  gotPredecessor = NULL;
{
  Join:
    if (self = 0){
        joined := TRUE;
    }else{
        actorInboxes[0] := Append(actorInboxes[0], <<"FindPredecessor", fingerStart(self, 1, bm), self>>);
        await predecessorAnswer # NULL /\ predecessorSuccessorAnswer # NULL;
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
         await fingerTables[self][fingerStart(self, 1, bm)] # NULL;
         if (between01(self, id, fingerTables[self][fingerStart(self, 1, bm)])){
             actorInboxes[asker] := 
             Append(actorInboxes[asker], <<"Predecessor", self,  fingerTables[self][fingerStart(self, 1, bm)]>>);
         } else {
             i := m;
             await fingerTables[self] # NULL;
             FindFirstSuitableI:
             while (i > 0 /\ ~(fingerStart(self, i, bm) \in DOMAIN fingerTables[self])){
                i := i - 1;
             };
             await fingerTables[self][fingerStart(self, i, bm)] # NULL;
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
                await gotPredecessor # NULL /\ fingerTables[self][fingerStart(self, 1, bm)] # NULL;
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
            if (predecessors[self] # NULL){
                if (between00(currentMessage[2], self, predecessors[self])){
                    predecessors[self] := currentMessage[2];
                };
            }; 
        };
         currentMessage := <<"?", NULL, NULL>>;
         kind := "?";
         id := NULL;
         asker := NULL;
    };   
};
};
*)
\* BEGIN TRANSLATION (chksum(pcal) = "a6b4c144" /\ chksum(tla) = "55f3fb71")
CONSTANT defaultInitValue
VARIABLES actorInboxes, triggered, fingerTables, predecessors, pc, 
          currentMessage, kind, id, asker, i, k, joined, predecessorAnswer, 
          predecessorSuccessorAnswer, gotPredecessor

vars == << actorInboxes, triggered, fingerTables, predecessors, pc, 
           currentMessage, kind, id, asker, i, k, joined, predecessorAnswer, 
           predecessorSuccessorAnswer, gotPredecessor >>

ProcSet == ({0, 1, 3})

Init == (* Global variables *)
        /\ actorInboxes = (0 :>  << <<"FindPredecessor", 6, 0>> >>) @@ (1 :>  <<>>) @@ (3 :> <<>>)
        /\ triggered = FALSE
        /\ fingerTables =                 (0 :> ((1 :> 0) @@ (2 :> 0) @@ (4 :> 0)))
                          @@ (1 :> ((2 :> NULL) @@ (3 :> NULL) @@ (5 :> NULL)))
                          @@ (3 :> ((4 :> NULL) @@ (5 :> NULL) @@ (7 :> NULL)))
        /\ predecessors = (0 :> 0) @@ (1 :> NULL) @@ (3 :> NULL)
        (* Process actor *)
        /\ currentMessage = [self \in {0, 1, 3} |-> <<"?", NULL, NULL>>]
        /\ kind = [self \in {0, 1, 3} |-> "?"]
        /\ id = [self \in {0, 1, 3} |-> NULL]
        /\ asker = [self \in {0, 1, 3} |-> NULL]
        /\ i = [self \in {0, 1, 3} |-> defaultInitValue]
        /\ k = [self \in {0, 1, 3} |-> defaultInitValue]
        /\ joined = [self \in {0, 1, 3} |-> FALSE]
        /\ predecessorAnswer = [self \in {0, 1, 3} |-> NULL]
        /\ predecessorSuccessorAnswer = [self \in {0, 1, 3} |-> NULL]
        /\ gotPredecessor = [self \in {0, 1, 3} |-> NULL]
        /\ pc = [self \in ProcSet |-> "Join"]

Join(self) == /\ pc[self] = "Join"
              /\ IF self = 0
                    THEN /\ joined' = [joined EXCEPT ![self] = TRUE]
                         /\ UNCHANGED << actorInboxes, fingerTables, 
                                         predecessors >>
                    ELSE /\ actorInboxes' = [actorInboxes EXCEPT ![0] = Append(actorInboxes[0], <<"FindPredecessor", fingerStart(self, 1, bm), self>>)]
                         /\ predecessorAnswer[self] # NULL /\ predecessorSuccessorAnswer[self] # NULL
                         /\ predecessors' = [predecessors EXCEPT ![self] = predecessorAnswer[self]]
                         /\ fingerTables' = [fingerTables EXCEPT ![self][fingerStart(self, 1, bm)] = predecessorSuccessorAnswer[self]]
                         /\ joined' = [joined EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "Stabilize"]
              /\ UNCHANGED << triggered, currentMessage, kind, id, asker, i, k, 
                              predecessorAnswer, predecessorSuccessorAnswer, 
                              gotPredecessor >>

Stabilize(self) == /\ pc[self] = "Stabilize"
                   /\ actorInboxes' = [actorInboxes EXCEPT ![self] = Append(actorInboxes[self], <<"Stabilize", 1>>)]
                   /\ pc' = [pc EXCEPT ![self] = "WaitForMessages"]
                   /\ UNCHANGED << triggered, fingerTables, predecessors, 
                                   currentMessage, kind, id, asker, i, k, 
                                   joined, predecessorAnswer, 
                                   predecessorSuccessorAnswer, gotPredecessor >>

WaitForMessages(self) == /\ pc[self] = "WaitForMessages"
                         /\ joined[self]
                         /\ pc' = [pc EXCEPT ![self] = "WhileAfterJoin"]
                         /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                                         predecessors, currentMessage, kind, 
                                         id, asker, i, k, joined, 
                                         predecessorAnswer, 
                                         predecessorSuccessorAnswer, 
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
                                        id, asker, i, k, joined, 
                                        predecessorAnswer, 
                                        predecessorSuccessorAnswer, 
                                        gotPredecessor >>

T1(self) == /\ pc[self] = "T1"
            /\ kind[self] = "FindPredecessor"
            /\ id' = [id EXCEPT ![self] = currentMessage[self][2]]
            /\ asker' = [asker EXCEPT ![self] = currentMessage[self][3]]
            /\ fingerTables[self][fingerStart(self, 1, bm)] # NULL
            /\ IF between01(self, id'[self], fingerTables[self][fingerStart(self, 1, bm)])
                  THEN /\ actorInboxes' = [actorInboxes EXCEPT ![asker'[self]] = Append(actorInboxes[asker'[self]], <<"Predecessor", self,  fingerTables[self][fingerStart(self, 1, bm)]>>)]
                       /\ pc' = [pc EXCEPT ![self] = "T2"]
                       /\ i' = i
                  ELSE /\ i' = [i EXCEPT ![self] = m]
                       /\ fingerTables[self] # NULL
                       /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                       /\ UNCHANGED actorInboxes
            /\ UNCHANGED << triggered, fingerTables, predecessors, 
                            currentMessage, kind, k, joined, predecessorAnswer, 
                            predecessorSuccessorAnswer, gotPredecessor >>

FindFirstSuitableI(self) == /\ pc[self] = "FindFirstSuitableI"
                            /\ IF i[self] > 0 /\ ~(fingerStart(self, i[self], bm) \in DOMAIN fingerTables[self])
                                  THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                                       /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                                  ELSE /\ fingerTables[self][fingerStart(self, i[self], bm)] # NULL
                                       /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                       /\ i' = i
                            /\ UNCHANGED << actorInboxes, triggered, 
                                            fingerTables, predecessors, 
                                            currentMessage, kind, id, asker, k, 
                                            joined, predecessorAnswer, 
                                            predecessorSuccessorAnswer, 
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
                                  currentMessage, kind, id, asker, k, joined, 
                                  predecessorAnswer, 
                                  predecessorSuccessorAnswer, gotPredecessor >>

FindSuitableI(self) == /\ pc[self] = "FindSuitableI"
                       /\ IF i[self] > 0 /\ ~(fingerStart(self, i[self], bm) \in DOMAIN fingerTables[self])
                             THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                                  /\ pc' = [pc EXCEPT ![self] = "FindSuitableI"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                  /\ i' = i
                       /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                                       predecessors, currentMessage, kind, id, 
                                       asker, k, joined, predecessorAnswer, 
                                       predecessorSuccessorAnswer, 
                                       gotPredecessor >>

T2(self) == /\ pc[self] = "T2"
            /\ kind[self] = "Predecessor"
            /\ predecessorAnswer' = [predecessorAnswer EXCEPT ![self] = currentMessage[self][2]]
            /\ predecessorSuccessorAnswer' = [predecessorSuccessorAnswer EXCEPT ![self] = currentMessage[self][3]]
            /\ pc' = [pc EXCEPT ![self] = "T3"]
            /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                            predecessors, currentMessage, kind, id, asker, i, 
                            k, joined, gotPredecessor >>

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
                         /\ gotPredecessor[self] # NULL /\ fingerTables[self][fingerStart(self, 1, bm)] # NULL
                         /\ IF between00(gotPredecessor[self], fingerTables[self][fingerStart(self, 1, bm)], self)
                               THEN /\ fingerTables' = [fingerTables EXCEPT ![self][fingerStart(self, 1, bm)] = gotPredecessor[self]]
                               ELSE /\ TRUE
                                    /\ UNCHANGED fingerTables
                         /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables'[self][fingerStart(self, 1, bm)]] = Append(actorInboxes[fingerTables'[self][fingerStart(self, 1, bm)]], <<"Notify", self>>)]
                         /\ pc' = [pc EXCEPT ![self] = "T4"]
                         /\ UNCHANGED << triggered, predecessors, 
                                         currentMessage, kind, id, asker, i, k, 
                                         joined, predecessorAnswer, 
                                         predecessorSuccessorAnswer, 
                                         gotPredecessor >>

T4(self) == /\ pc[self] = "T4"
            /\ kind[self] = "GetPredecessor"
            /\ actorInboxes' = [actorInboxes EXCEPT ![currentMessage[self][2]] = Append(actorInboxes[currentMessage[self][2]], <<"GotPredecessor", predecessors[self]>>)]
            /\ pc' = [pc EXCEPT ![self] = "T5"]
            /\ UNCHANGED << triggered, fingerTables, predecessors, 
                            currentMessage, kind, id, asker, i, k, joined, 
                            predecessorAnswer, predecessorSuccessorAnswer, 
                            gotPredecessor >>

T5(self) == /\ pc[self] = "T5"
            /\ kind[self] = "GotPredecessor"
            /\ gotPredecessor' = [gotPredecessor EXCEPT ![self] = currentMessage[self][2]]
            /\ pc' = [pc EXCEPT ![self] = "T6"]
            /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                            predecessors, currentMessage, kind, id, asker, i, 
                            k, joined, predecessorAnswer, 
                            predecessorSuccessorAnswer >>

T6(self) == /\ pc[self] = "T6"
            /\ kind[self] = "Notify"
            /\ IF predecessors[self] # NULL
                  THEN /\ IF between00(currentMessage[self][2], self, predecessors[self])
                             THEN /\ predecessors' = [predecessors EXCEPT ![self] = currentMessage[self][2]]
                             ELSE /\ TRUE
                                  /\ UNCHANGED predecessors
                  ELSE /\ TRUE
                       /\ UNCHANGED predecessors
            /\ currentMessage' = [currentMessage EXCEPT ![self] = <<"?", NULL, NULL>>]
            /\ kind' = [kind EXCEPT ![self] = "?"]
            /\ id' = [id EXCEPT ![self] = NULL]
            /\ asker' = [asker EXCEPT ![self] = NULL]
            /\ pc' = [pc EXCEPT ![self] = "WhileAfterJoin"]
            /\ UNCHANGED << actorInboxes, triggered, fingerTables, i, k, 
                            joined, predecessorAnswer, 
                            predecessorSuccessorAnswer, gotPredecessor >>

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

Liveness == []Triggered

LenStateConstraint == Len(actorInboxes[0])<=1 /\ Len(actorInboxes[1])<=1 /\ Len(actorInboxes[3])<=1

=============================================================================
\* Modification History
\* Last modified Thu Apr 07 01:32:55 YEKT 2022 by pervu
\* Created Sun Jan 30 18:34:11 YEKT 2022 by pervu
