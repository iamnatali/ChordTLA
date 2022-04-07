------------------------------- MODULE actor -------------------------------
EXTENDS TLC, Integers, Sequences

between01(n1, nb, n2) == (nb >= 0) /\ (((n1 < n2) /\ ((n1 < nb) /\ (nb <= n2))) \/ ((n1 >= n2) /\ ((n1 < nb) \/ (nb <= n2))))
between00(n1, nb, n2) == (nb >= 0) /\ (((n1 < n2) /\ ((n1 < nb) /\ (nb < n2))) \/ ((n1 >= n2) /\ ((n1 < nb) \/ (nb < n2))))

fingerStart(myId, k, m) == (myId + (2^(k-1)))%m

CONSTANTS m, bm, NULL

(*--fair algorithm ActorStuff {
variables actorInboxes = (0 :>  <<>>) @@ (1 :>  <<>>) @@ (3 :> <<>>);
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
    };
  WaitForMessagesBeforeJoin:+
    if (joined # TRUE){
        WhileWaitForMessagesBeforeJoin:+
        while (TRUE) {
        if (actorInboxes[self] /= <<>>) {
         currentMessage := Head(actorInboxes[self]);
         kind := Head(currentMessage);
         actorInboxes[self] := Tail(actorInboxes[self]);
        };
        ProcessMessageBeforeJoin:+
        {
            if (kind = "Predecessor"){
                predecessorAnswer := currentMessage[2];
                predecessorSuccessorAnswer := currentMessage[3];
                predecessors[self] := predecessorAnswer;
                fingerTables[self][fingerStart(self, 1, bm)] := predecessorSuccessorAnswer;
                joined := TRUE;
             }
        };
        ReturnDefaultsBeforeJoin:
         currentMessage := <<"?", NULL, NULL>>;
         kind := "?";
         id := NULL;
         asker := NULL;
    };
    };
  Stabilize:+
    if (joined){
        actorInboxes[self] := Append(actorInboxes[self], <<"Stabilize", 1>>);
    };
  WaitForMessages:+
    if (joined)
    {
    WhileWaitForMessages:+
      while (TRUE) {
      if (actorInboxes[self] /= <<>>) {
         currentMessage := Head(actorInboxes[self]);
         kind := Head(currentMessage);
         actorInboxes[self] := Tail(actorInboxes[self]);
        };
        ProcessMessage:+
        {
         if (kind = "FindPredecessor"){
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
         } else {
             {
                 if (kind = "Stabilize") {
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
                 } else {
                     if (kind = "GetPredecessor") {
                         actorInboxes[currentMessage[2]] := 
                         Append(actorInboxes[currentMessage[2]], <<"GotPredecessor", predecessors[self]>>);
                     } else {
                         if (kind = "GotPredecessor") {
                             gotPredecessor := currentMessage[2];
                         } else {
                             if (kind = "Notify") {
                                 if (predecessors[self] # NULL){
                                    if (between00(currentMessage[2], self, predecessors[self])){
                                        predecessors[self] := currentMessage[2];
                                    };
                                };
                             }
                         }
                     }
                 }
             }
         };   
        };
        ReturnDefaults:
         currentMessage := <<"?", NULL, NULL>>;
         kind := "?";
         id := NULL;
         asker := NULL;
        };
    };   
};
};
*)
\* BEGIN TRANSLATION (chksum(pcal) = "f3431d41" /\ chksum(tla) = "a7b0d2f")
CONSTANT defaultInitValue
VARIABLES actorInboxes, triggered, fingerTables, predecessors, pc, 
          currentMessage, kind, id, asker, i, k, joined, predecessorAnswer, 
          predecessorSuccessorAnswer, gotPredecessor

vars == << actorInboxes, triggered, fingerTables, predecessors, pc, 
           currentMessage, kind, id, asker, i, k, joined, predecessorAnswer, 
           predecessorSuccessorAnswer, gotPredecessor >>

ProcSet == ({0, 1, 3})

Init == (* Global variables *)
        /\ actorInboxes = (0 :>  <<>>) @@ (1 :>  <<>>) @@ (3 :> <<>>)
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
                         /\ UNCHANGED actorInboxes
                    ELSE /\ actorInboxes' = [actorInboxes EXCEPT ![0] = Append(actorInboxes[0], <<"FindPredecessor", fingerStart(self, 1, bm), self>>)]
                         /\ UNCHANGED joined
              /\ pc' = [pc EXCEPT ![self] = "WaitForMessagesBeforeJoin"]
              /\ UNCHANGED << triggered, fingerTables, predecessors, 
                              currentMessage, kind, id, asker, i, k, 
                              predecessorAnswer, predecessorSuccessorAnswer, 
                              gotPredecessor >>

WaitForMessagesBeforeJoin(self) == /\ pc[self] = "WaitForMessagesBeforeJoin"
                                   /\ IF joined[self] # TRUE
                                         THEN /\ pc' = [pc EXCEPT ![self] = "WhileWaitForMessagesBeforeJoin"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Stabilize"]
                                   /\ UNCHANGED << actorInboxes, triggered, 
                                                   fingerTables, predecessors, 
                                                   currentMessage, kind, id, 
                                                   asker, i, k, joined, 
                                                   predecessorAnswer, 
                                                   predecessorSuccessorAnswer, 
                                                   gotPredecessor >>

WhileWaitForMessagesBeforeJoin(self) == /\ pc[self] = "WhileWaitForMessagesBeforeJoin"
                                        /\ IF actorInboxes[self] /= <<>>
                                              THEN /\ currentMessage' = [currentMessage EXCEPT ![self] = Head(actorInboxes[self])]
                                                   /\ kind' = [kind EXCEPT ![self] = Head(currentMessage'[self])]
                                                   /\ actorInboxes' = [actorInboxes EXCEPT ![self] = Tail(actorInboxes[self])]
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED << actorInboxes, 
                                                                   currentMessage, 
                                                                   kind >>
                                        /\ pc' = [pc EXCEPT ![self] = "ProcessMessageBeforeJoin"]
                                        /\ UNCHANGED << triggered, 
                                                        fingerTables, 
                                                        predecessors, id, 
                                                        asker, i, k, joined, 
                                                        predecessorAnswer, 
                                                        predecessorSuccessorAnswer, 
                                                        gotPredecessor >>

ProcessMessageBeforeJoin(self) == /\ pc[self] = "ProcessMessageBeforeJoin"
                                  /\ IF kind[self] = "Predecessor"
                                        THEN /\ predecessorAnswer' = [predecessorAnswer EXCEPT ![self] = currentMessage[self][2]]
                                             /\ predecessorSuccessorAnswer' = [predecessorSuccessorAnswer EXCEPT ![self] = currentMessage[self][3]]
                                             /\ predecessors' = [predecessors EXCEPT ![self] = predecessorAnswer'[self]]
                                             /\ fingerTables' = [fingerTables EXCEPT ![self][fingerStart(self, 1, bm)] = predecessorSuccessorAnswer'[self]]
                                             /\ joined' = [joined EXCEPT ![self] = TRUE]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << fingerTables, 
                                                             predecessors, 
                                                             joined, 
                                                             predecessorAnswer, 
                                                             predecessorSuccessorAnswer >>
                                  /\ pc' = [pc EXCEPT ![self] = "ReturnDefaultsBeforeJoin"]
                                  /\ UNCHANGED << actorInboxes, triggered, 
                                                  currentMessage, kind, id, 
                                                  asker, i, k, gotPredecessor >>

ReturnDefaultsBeforeJoin(self) == /\ pc[self] = "ReturnDefaultsBeforeJoin"
                                  /\ currentMessage' = [currentMessage EXCEPT ![self] = <<"?", NULL, NULL>>]
                                  /\ kind' = [kind EXCEPT ![self] = "?"]
                                  /\ id' = [id EXCEPT ![self] = NULL]
                                  /\ asker' = [asker EXCEPT ![self] = NULL]
                                  /\ pc' = [pc EXCEPT ![self] = "WhileWaitForMessagesBeforeJoin"]
                                  /\ UNCHANGED << actorInboxes, triggered, 
                                                  fingerTables, predecessors, 
                                                  i, k, joined, 
                                                  predecessorAnswer, 
                                                  predecessorSuccessorAnswer, 
                                                  gotPredecessor >>

Stabilize(self) == /\ pc[self] = "Stabilize"
                   /\ IF joined[self]
                         THEN /\ actorInboxes' = [actorInboxes EXCEPT ![self] = Append(actorInboxes[self], <<"Stabilize", 1>>)]
                         ELSE /\ TRUE
                              /\ UNCHANGED actorInboxes
                   /\ pc' = [pc EXCEPT ![self] = "WaitForMessages"]
                   /\ UNCHANGED << triggered, fingerTables, predecessors, 
                                   currentMessage, kind, id, asker, i, k, 
                                   joined, predecessorAnswer, 
                                   predecessorSuccessorAnswer, gotPredecessor >>

WaitForMessages(self) == /\ pc[self] = "WaitForMessages"
                         /\ IF joined[self]
                               THEN /\ pc' = [pc EXCEPT ![self] = "WhileWaitForMessages"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                                         predecessors, currentMessage, kind, 
                                         id, asker, i, k, joined, 
                                         predecessorAnswer, 
                                         predecessorSuccessorAnswer, 
                                         gotPredecessor >>

WhileWaitForMessages(self) == /\ pc[self] = "WhileWaitForMessages"
                              /\ IF actorInboxes[self] /= <<>>
                                    THEN /\ currentMessage' = [currentMessage EXCEPT ![self] = Head(actorInboxes[self])]
                                         /\ kind' = [kind EXCEPT ![self] = Head(currentMessage'[self])]
                                         /\ actorInboxes' = [actorInboxes EXCEPT ![self] = Tail(actorInboxes[self])]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED << actorInboxes, 
                                                         currentMessage, kind >>
                              /\ pc' = [pc EXCEPT ![self] = "ProcessMessage"]
                              /\ UNCHANGED << triggered, fingerTables, 
                                              predecessors, id, asker, i, k, 
                                              joined, predecessorAnswer, 
                                              predecessorSuccessorAnswer, 
                                              gotPredecessor >>

ProcessMessage(self) == /\ pc[self] = "ProcessMessage"
                        /\ IF kind[self] = "FindPredecessor"
                              THEN /\ id' = [id EXCEPT ![self] = currentMessage[self][2]]
                                   /\ asker' = [asker EXCEPT ![self] = currentMessage[self][3]]
                                   /\ fingerTables[self][fingerStart(self, 1, bm)] # NULL
                                   /\ IF between01(self, id'[self], fingerTables[self][fingerStart(self, 1, bm)])
                                         THEN /\ actorInboxes' = [actorInboxes EXCEPT ![asker'[self]] = Append(actorInboxes[asker'[self]], <<"Predecessor", self,  fingerTables[self][fingerStart(self, 1, bm)]>>)]
                                              /\ pc' = [pc EXCEPT ![self] = "ReturnDefaults"]
                                              /\ i' = i
                                         ELSE /\ i' = [i EXCEPT ![self] = m]
                                              /\ fingerTables[self] # NULL
                                              /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                                              /\ UNCHANGED actorInboxes
                                   /\ UNCHANGED << predecessors, k, 
                                                   gotPredecessor >>
                              ELSE /\ IF kind[self] = "Stabilize"
                                         THEN /\ k' = [k EXCEPT ![self] = currentMessage[self][2]]
                                              /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables[self][fingerStart(self, k'[self], bm)]] = Append(actorInboxes[fingerTables[self][fingerStart(self, k'[self], bm)]], <<"GetPredecessor", self>>)]
                                              /\ pc' = [pc EXCEPT ![self] = "FinishStabilize"]
                                              /\ UNCHANGED << predecessors, 
                                                              gotPredecessor >>
                                         ELSE /\ IF kind[self] = "GetPredecessor"
                                                    THEN /\ actorInboxes' = [actorInboxes EXCEPT ![currentMessage[self][2]] = Append(actorInboxes[currentMessage[self][2]], <<"GotPredecessor", predecessors[self]>>)]
                                                         /\ UNCHANGED << predecessors, 
                                                                         gotPredecessor >>
                                                    ELSE /\ IF kind[self] = "GotPredecessor"
                                                               THEN /\ gotPredecessor' = [gotPredecessor EXCEPT ![self] = currentMessage[self][2]]
                                                                    /\ UNCHANGED predecessors
                                                               ELSE /\ IF kind[self] = "Notify"
                                                                          THEN /\ IF predecessors[self] # NULL
                                                                                     THEN /\ IF between00(currentMessage[self][2], self, predecessors[self])
                                                                                                THEN /\ predecessors' = [predecessors EXCEPT ![self] = currentMessage[self][2]]
                                                                                                ELSE /\ TRUE
                                                                                                     /\ UNCHANGED predecessors
                                                                                     ELSE /\ TRUE
                                                                                          /\ UNCHANGED predecessors
                                                                          ELSE /\ TRUE
                                                                               /\ UNCHANGED predecessors
                                                                    /\ UNCHANGED gotPredecessor
                                                         /\ UNCHANGED actorInboxes
                                              /\ pc' = [pc EXCEPT ![self] = "ReturnDefaults"]
                                              /\ k' = k
                                   /\ UNCHANGED << id, asker, i >>
                        /\ UNCHANGED << triggered, fingerTables, 
                                        currentMessage, kind, joined, 
                                        predecessorAnswer, 
                                        predecessorSuccessorAnswer >>

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
                             /\ pc' = [pc EXCEPT ![self] = "ReturnDefaults"]
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

FinishStabilize(self) == /\ pc[self] = "FinishStabilize"
                         /\ gotPredecessor[self] # NULL /\ fingerTables[self][fingerStart(self, 1, bm)] # NULL
                         /\ IF between00(gotPredecessor[self], fingerTables[self][fingerStart(self, 1, bm)], self)
                               THEN /\ fingerTables' = [fingerTables EXCEPT ![self][fingerStart(self, 1, bm)] = gotPredecessor[self]]
                               ELSE /\ TRUE
                                    /\ UNCHANGED fingerTables
                         /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables'[self][fingerStart(self, 1, bm)]] = Append(actorInboxes[fingerTables'[self][fingerStart(self, 1, bm)]], <<"Notify", self>>)]
                         /\ pc' = [pc EXCEPT ![self] = "ReturnDefaults"]
                         /\ UNCHANGED << triggered, predecessors, 
                                         currentMessage, kind, id, asker, i, k, 
                                         joined, predecessorAnswer, 
                                         predecessorSuccessorAnswer, 
                                         gotPredecessor >>

ReturnDefaults(self) == /\ pc[self] = "ReturnDefaults"
                        /\ currentMessage' = [currentMessage EXCEPT ![self] = <<"?", NULL, NULL>>]
                        /\ kind' = [kind EXCEPT ![self] = "?"]
                        /\ id' = [id EXCEPT ![self] = NULL]
                        /\ asker' = [asker EXCEPT ![self] = NULL]
                        /\ pc' = [pc EXCEPT ![self] = "WhileWaitForMessages"]
                        /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                                        predecessors, i, k, joined, 
                                        predecessorAnswer, 
                                        predecessorSuccessorAnswer, 
                                        gotPredecessor >>

actor(self) == Join(self) \/ WaitForMessagesBeforeJoin(self)
                  \/ WhileWaitForMessagesBeforeJoin(self)
                  \/ ProcessMessageBeforeJoin(self)
                  \/ ReturnDefaultsBeforeJoin(self) \/ Stabilize(self)
                  \/ WaitForMessages(self) \/ WhileWaitForMessages(self)
                  \/ ProcessMessage(self) \/ FindFirstSuitableI(self)
                  \/ MainLoop(self) \/ FindSuitableI(self)
                  \/ FinishStabilize(self) \/ ReturnDefaults(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {0, 1, 3}: actor(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in {0, 1, 3} : /\ WF_vars(actor(self))
                                   /\ SF_vars(WaitForMessagesBeforeJoin(self)) /\ SF_vars(WhileWaitForMessagesBeforeJoin(self)) /\ SF_vars(ProcessMessageBeforeJoin(self)) /\ SF_vars(Stabilize(self)) /\ SF_vars(WaitForMessages(self)) /\ SF_vars(WhileWaitForMessages(self)) /\ SF_vars(ProcessMessage(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Triggered == predecessors = (0 :> 0) @@ (1 :> 0) @@ (3 :> 0)

Liveness == <>Triggered

LenStateConstraint == Len(actorInboxes[0])<=2 /\ Len(actorInboxes[1])<=2 /\ Len(actorInboxes[3])<=2

=============================================================================
\* Modification History
\* Last modified Thu Apr 07 09:11:32 YEKT 2022 by pervu
\* Created Sun Jan 30 18:34:11 YEKT 2022 by pervu
