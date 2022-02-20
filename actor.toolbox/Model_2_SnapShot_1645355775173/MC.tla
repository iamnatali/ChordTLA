---- MODULE MC ----
EXTENDS actor, TLC

\* CONSTANT definitions @modelParameterConstants:0bm
const_1645355770075114000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:1m
const_1645355770075115000 == 
3
----

\* CONSTANT definitions @modelParameterConstants:3fingerTables
const_1645355770075116000 == 
 (0 :> ((1 :> 1) @@ (2 :> 3) @@ (4 :> 0))) 
          @@ (1 :> ((2 :> 3) @@ (3 :> 5) @@ (5 :> 0)))
          @@ (3 :> ((4 :> 0) @@ (5 :> 0) @@ (7 :> 0)))
----

=============================================================================
\* Modification History
\* Created Sun Feb 20 16:16:10 YEKT 2022 by pervu
