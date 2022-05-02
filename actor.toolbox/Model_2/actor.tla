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
  i;
  joined = FALSE;
{
  Join:+
    if (self = 0){
        joined := TRUE;
    }else{
        actorInboxes[0] := Append(actorInboxes[0], <<"FindPredecessor", fingerStart(self, 1, bm), self>>);
    };
  WaitForMessagesBeforeJoin:+
    if (joined # TRUE){
        await actorInboxes[self] /= <<>>; 
        {
         currentMessage := Head(actorInboxes[self]);
         kind := Head(currentMessage);
         actorInboxes[self] := Tail(actorInboxes[self]);
        };
        ProcessMessageBeforeJoin:+
        {
            if (kind = "Predecessor"){
                predecessors[self] := currentMessage[2];
                fingerTables[self][fingerStart(self, 1, bm)] := currentMessage[3];
                joined := TRUE;
             }
        };
        ReturnDefaultsBeforeJoin:+{
         currentMessage := <<"?", NULL, NULL>>;
         kind := "?";
         id := NULL;
         };
    };
  Stabilize:+
    if (joined){
        actorInboxes[self] := Append(actorInboxes[self], <<"Stabilize", 1>>);
    };
  WaitForMessages:+
    if (joined)
    {
      {
      await actorInboxes[self] /= <<>>; 
      {
         currentMessage := Head(actorInboxes[self]);
         kind := Head(currentMessage);
         actorInboxes[self] := Tail(actorInboxes[self]);
        };
        ProcessMessage:+
        {
         if (kind = "FindPredecessor"){
             id := currentMessage[2];
         \*await fingerTables[self][fingerStart(self, 1, bm)] # NULL;
         if (between01(self, id, fingerTables[self][fingerStart(self, 1, bm)])){
             actorInboxes[currentMessage[3]] := 
             Append(actorInboxes[currentMessage[3]], <<"Predecessor", self,  fingerTables[self][fingerStart(self, 1, bm)]>>);
         } else {
             i := m;
             \*await fingerTables[self] # NULL;
             FindFirstSuitableI:
             while (i > 0 /\ ~(fingerStart(self, i, bm) \in DOMAIN fingerTables[self])){
                i := i - 1;
             };
             \*await fingerTables[self][fingerStart(self, i, bm)] # NULL;
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
                    actorInboxes[fingerTables[self][fingerStart(self, currentMessage[2], bm)]] := 
                    Append(actorInboxes[fingerTables[self][fingerStart(self, currentMessage[2], bm)]], <<"GetPredecessor", self>>);
                 } else {
                     if (kind = "GetPredecessor") {
                         actorInboxes[currentMessage[2]] := 
                         Append(actorInboxes[currentMessage[2]], <<"GotPredecessor", predecessors[self]>>);
                     } else {
                         if (kind = "GotPredecessor") {    
                            if (between00(currentMessage[2], fingerTables[self][fingerStart(self, 1, bm)], self)){
                                fingerTables[self][fingerStart(self, 1, bm)] := currentMessage[2];
                            };
                            actorInboxes[fingerTables[self][fingerStart(self, 1, bm)]] := 
                            Append(actorInboxes[fingerTables[self][fingerStart(self, 1, bm)]], <<"Notify", self>>);
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
        ReturnDefaults:+{
         currentMessage := <<"?", NULL, NULL>>;
         kind := "?";
         id := NULL;
         };
        };
    };   
};
};
*)
\* BEGIN TRANSLATION (chksum(pcal) = "e76f72bb" /\ chksum(tla) = "6a8eed9d")
CONSTANT defaultInitValue
VARIABLES actorInboxes, triggered, fingerTables, predecessors, pc, 
          currentMessage, kind, id, i, joined

vars == << actorInboxes, triggered, fingerTables, predecessors, pc, 
           currentMessage, kind, id, i, joined >>

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
        /\ i = [self \in {0, 1, 3} |-> defaultInitValue]
        /\ joined = [self \in {0, 1, 3} |-> FALSE]
        /\ pc = [self \in ProcSet |-> "Join"]

Join(self) == /\ pc[self] = "Join"
              /\ IF self = 0
                    THEN /\ joined' = [joined EXCEPT ![self] = TRUE]
                         /\ UNCHANGED actorInboxes
                    ELSE /\ actorInboxes' = [actorInboxes EXCEPT ![0] = Append(actorInboxes[0], <<"FindPredecessor", fingerStart(self, 1, bm), self>>)]
                         /\ UNCHANGED joined
              /\ pc' = [pc EXCEPT ![self] = "WaitForMessagesBeforeJoin"]
              /\ UNCHANGED << triggered, fingerTables, predecessors, 
                              currentMessage, kind, id, i >>

WaitForMessagesBeforeJoin(self) == /\ pc[self] = "WaitForMessagesBeforeJoin"
                                   /\ IF joined[self] # TRUE
                                         THEN /\ actorInboxes[self] /= <<>>
                                              /\ currentMessage' = [currentMessage EXCEPT ![self] = Head(actorInboxes[self])]
                                              /\ kind' = [kind EXCEPT ![self] = Head(currentMessage'[self])]
                                              /\ actorInboxes' = [actorInboxes EXCEPT ![self] = Tail(actorInboxes[self])]
                                              /\ pc' = [pc EXCEPT ![self] = "ProcessMessageBeforeJoin"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "Stabilize"]
                                              /\ UNCHANGED << actorInboxes, 
                                                              currentMessage, 
                                                              kind >>
                                   /\ UNCHANGED << triggered, fingerTables, 
                                                   predecessors, id, i, joined >>

ProcessMessageBeforeJoin(self) == /\ pc[self] = "ProcessMessageBeforeJoin"
                                  /\ IF kind[self] = "Predecessor"
                                        THEN /\ predecessors' = [predecessors EXCEPT ![self] = currentMessage[self][2]]
                                             /\ fingerTables' = [fingerTables EXCEPT ![self][fingerStart(self, 1, bm)] = currentMessage[self][3]]
                                             /\ joined' = [joined EXCEPT ![self] = TRUE]
                                        ELSE /\ TRUE
                                             /\ UNCHANGED << fingerTables, 
                                                             predecessors, 
                                                             joined >>
                                  /\ pc' = [pc EXCEPT ![self] = "ReturnDefaultsBeforeJoin"]
                                  /\ UNCHANGED << actorInboxes, triggered, 
                                                  currentMessage, kind, id, i >>

ReturnDefaultsBeforeJoin(self) == /\ pc[self] = "ReturnDefaultsBeforeJoin"
                                  /\ currentMessage' = [currentMessage EXCEPT ![self] = <<"?", NULL, NULL>>]
                                  /\ kind' = [kind EXCEPT ![self] = "?"]
                                  /\ id' = [id EXCEPT ![self] = NULL]
                                  /\ pc' = [pc EXCEPT ![self] = "Stabilize"]
                                  /\ UNCHANGED << actorInboxes, triggered, 
                                                  fingerTables, predecessors, 
                                                  i, joined >>

Stabilize(self) == /\ pc[self] = "Stabilize"
                   /\ IF joined[self]
                         THEN /\ actorInboxes' = [actorInboxes EXCEPT ![self] = Append(actorInboxes[self], <<"Stabilize", 1>>)]
                         ELSE /\ TRUE
                              /\ UNCHANGED actorInboxes
                   /\ pc' = [pc EXCEPT ![self] = "WaitForMessages"]
                   /\ UNCHANGED << triggered, fingerTables, predecessors, 
                                   currentMessage, kind, id, i, joined >>

WaitForMessages(self) == /\ pc[self] = "WaitForMessages"
                         /\ IF joined[self]
                               THEN /\ actorInboxes[self] /= <<>>
                                    /\ currentMessage' = [currentMessage EXCEPT ![self] = Head(actorInboxes[self])]
                                    /\ kind' = [kind EXCEPT ![self] = Head(currentMessage'[self])]
                                    /\ actorInboxes' = [actorInboxes EXCEPT ![self] = Tail(actorInboxes[self])]
                                    /\ pc' = [pc EXCEPT ![self] = "ProcessMessage"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED << actorInboxes, 
                                                    currentMessage, kind >>
                         /\ UNCHANGED << triggered, fingerTables, predecessors, 
                                         id, i, joined >>

ProcessMessage(self) == /\ pc[self] = "ProcessMessage"
                        /\ IF kind[self] = "FindPredecessor"
                              THEN /\ id' = [id EXCEPT ![self] = currentMessage[self][2]]
                                   /\ IF between01(self, id'[self], fingerTables[self][fingerStart(self, 1, bm)])
                                         THEN /\ actorInboxes' = [actorInboxes EXCEPT ![currentMessage[self][3]] = Append(actorInboxes[currentMessage[self][3]], <<"Predecessor", self,  fingerTables[self][fingerStart(self, 1, bm)]>>)]
                                              /\ pc' = [pc EXCEPT ![self] = "ReturnDefaults"]
                                              /\ i' = i
                                         ELSE /\ i' = [i EXCEPT ![self] = m]
                                              /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                                              /\ UNCHANGED actorInboxes
                                   /\ UNCHANGED << fingerTables, predecessors >>
                              ELSE /\ IF kind[self] = "Stabilize"
                                         THEN /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables[self][fingerStart(self, currentMessage[self][2], bm)]] = Append(actorInboxes[fingerTables[self][fingerStart(self, currentMessage[self][2], bm)]], <<"GetPredecessor", self>>)]
                                              /\ UNCHANGED << fingerTables, 
                                                              predecessors >>
                                         ELSE /\ IF kind[self] = "GetPredecessor"
                                                    THEN /\ actorInboxes' = [actorInboxes EXCEPT ![currentMessage[self][2]] = Append(actorInboxes[currentMessage[self][2]], <<"GotPredecessor", predecessors[self]>>)]
                                                         /\ UNCHANGED << fingerTables, 
                                                                         predecessors >>
                                                    ELSE /\ IF kind[self] = "GotPredecessor"
                                                               THEN /\ IF between00(currentMessage[self][2], fingerTables[self][fingerStart(self, 1, bm)], self)
                                                                          THEN /\ fingerTables' = [fingerTables EXCEPT ![self][fingerStart(self, 1, bm)] = currentMessage[self][2]]
                                                                          ELSE /\ TRUE
                                                                               /\ UNCHANGED fingerTables
                                                                    /\ actorInboxes' = [actorInboxes EXCEPT ![fingerTables'[self][fingerStart(self, 1, bm)]] = Append(actorInboxes[fingerTables'[self][fingerStart(self, 1, bm)]], <<"Notify", self>>)]
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
                                                                    /\ UNCHANGED << actorInboxes, 
                                                                                    fingerTables >>
                                   /\ pc' = [pc EXCEPT ![self] = "ReturnDefaults"]
                                   /\ UNCHANGED << id, i >>
                        /\ UNCHANGED << triggered, currentMessage, kind, 
                                        joined >>

FindFirstSuitableI(self) == /\ pc[self] = "FindFirstSuitableI"
                            /\ IF i[self] > 0 /\ ~(fingerStart(self, i[self], bm) \in DOMAIN fingerTables[self])
                                  THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                                       /\ pc' = [pc EXCEPT ![self] = "FindFirstSuitableI"]
                                  ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                       /\ i' = i
                            /\ UNCHANGED << actorInboxes, triggered, 
                                            fingerTables, predecessors, 
                                            currentMessage, kind, id, joined >>

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
                                  currentMessage, kind, id, joined >>

FindSuitableI(self) == /\ pc[self] = "FindSuitableI"
                       /\ IF i[self] > 0 /\ ~(fingerStart(self, i[self], bm) \in DOMAIN fingerTables[self])
                             THEN /\ i' = [i EXCEPT ![self] = i[self] - 1]
                                  /\ pc' = [pc EXCEPT ![self] = "FindSuitableI"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "MainLoop"]
                                  /\ i' = i
                       /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                                       predecessors, currentMessage, kind, id, 
                                       joined >>

ReturnDefaults(self) == /\ pc[self] = "ReturnDefaults"
                        /\ currentMessage' = [currentMessage EXCEPT ![self] = <<"?", NULL, NULL>>]
                        /\ kind' = [kind EXCEPT ![self] = "?"]
                        /\ id' = [id EXCEPT ![self] = NULL]
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << actorInboxes, triggered, fingerTables, 
                                        predecessors, i, joined >>

actor(self) == Join(self) \/ WaitForMessagesBeforeJoin(self)
                  \/ ProcessMessageBeforeJoin(self)
                  \/ ReturnDefaultsBeforeJoin(self) \/ Stabilize(self)
                  \/ WaitForMessages(self) \/ ProcessMessage(self)
                  \/ FindFirstSuitableI(self) \/ MainLoop(self)
                  \/ FindSuitableI(self) \/ ReturnDefaults(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {0, 1, 3}: actor(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in {0, 1, 3} : /\ WF_vars(actor(self))
                                   /\ SF_vars(Join(self)) /\ SF_vars(WaitForMessagesBeforeJoin(self)) /\ SF_vars(ProcessMessageBeforeJoin(self)) /\ SF_vars(ReturnDefaultsBeforeJoin(self)) /\ SF_vars(Stabilize(self)) /\ SF_vars(WaitForMessages(self)) /\ SF_vars(ProcessMessage(self)) /\ SF_vars(ReturnDefaults(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Triggered == predecessors = (0 :> 0) @@ (1 :> 0) @@ (3 :> 0)

Liveness == <>Triggered

LenStateConstraint == Len(actorInboxes[0])<=0 /\ Len(actorInboxes[1])<=0 /\ Len(actorInboxes[3])<=0

=============================================================================
\* Modification History
\* Last modified Sun May 01 22:55:46 YEKT 2022 by pervu
\* Created Sun Jan 30 18:34:11 YEKT 2022 by pervu
