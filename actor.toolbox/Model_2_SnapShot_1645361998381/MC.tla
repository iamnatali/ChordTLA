---- MODULE MC ----
EXTENDS actor, TLC

\* CONSTANT definitions @modelParameterConstants:0bm
const_1645361993184122000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:1m
const_1645361993184123000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3fingerTables
const_1645361993184124000 == 
 (0 :> ((1 :> 1) @@ (2 :> 3) @@ (4 :> 0))) 
          @@ (1 :> ((2 :> 3) @@ (3 :> 5) @@ (5 :> 0)))
          @@ (3 :> ((4 :> 0) @@ (5 :> 0) @@ (7 :> 0)))
----

=============================================================================
\* Modification History
\* Created Sun Feb 20 17:59:53 YEKT 2022 by pervu
