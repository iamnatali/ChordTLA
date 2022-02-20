---- MODULE MC ----
EXTENDS actor, TLC

\* CONSTANT definitions @modelParameterConstants:0bm
const_164534848610285000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:1m
const_164534848610286000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3fingerTables
const_164534848610287000 == 
 (0 :> ((1 :> 1) @@ (2 :> 3) @@ (4 :> 0))) 
          @@ (1 :> ((2 :> 3) @@ (3 :> 5) @@ (5 :> 0)))
          @@ (3 :> ((4 :> 0) @@ (5 :> 0) @@ (7 :> 0)))
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_164534848610288000 ==
Len(actorInboxes[0])<5 /\ Len(actorInboxes[1])<5 /\ Len(actorInboxes[3])<5
----
=============================================================================
\* Modification History
\* Created Sun Feb 20 14:14:46 YEKT 2022 by pervu
