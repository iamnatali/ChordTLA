---- MODULE MC ----
EXTENDS actor, TLC

\* CONSTANT definitions @modelParameterConstants:0bm
const_1645348968797105000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:1m
const_1645348968797106000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3fingerTables
const_1645348968797107000 == 
 (0 :> ((1 :> 1) @@ (2 :> 3) @@ (4 :> 0))) 
          @@ (1 :> ((2 :> 3) @@ (3 :> 5) @@ (5 :> 0)))
          @@ (3 :> ((4 :> 0) @@ (5 :> 0) @@ (7 :> 0)))
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_1645348968797108000 ==
Len(actorInboxes[0])<=1 /\ Len(actorInboxes[1])<=1 /\ Len(actorInboxes[3])<=1
----
=============================================================================
\* Modification History
\* Created Sun Feb 20 14:22:48 YEKT 2022 by pervu
