---- MODULE MC ----
EXTENDS actor, TLC

\* CONSTANT definitions @modelParameterConstants:0bm
const_164930440367620000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:1m
const_164930440367621000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_164930440367622000 ==
LenStateConstraint
----
\* Constant expression definition @modelExpressionEval
const_expr_164930440367623000 == 
1
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_164930440367623000>>)
----

=============================================================================
\* Modification History
\* Created Thu Apr 07 09:06:43 YEKT 2022 by pervu
