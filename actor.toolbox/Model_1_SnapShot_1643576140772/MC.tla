---- MODULE MC ----
EXTENDS actor, TLC

\* Constant expression definition @modelExpressionEval
const_expr_16435761363975000 == 
<<"FindPredecessor", 6, 0>>[2]
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_16435761363975000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_16435761363976000 ==
FALSE/\stack = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_16435761363977000 ==
FALSE/\stack' = stack
----
=============================================================================
\* Modification History
\* Created Mon Jan 31 01:55:36 YEKT 2022 by pervu
