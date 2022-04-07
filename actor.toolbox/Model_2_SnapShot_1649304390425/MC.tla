---- MODULE MC ----
EXTENDS actor, TLC

\* CONSTANT definitions @modelParameterConstants:0bm
const_164930436611515000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:1m
const_164930436611516000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_164930436611517000 ==
LenStateConstraint
----
\* Constant expression definition @modelExpressionEval
const_expr_164930436611518000 == 
1
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_164930436611518000>>)
----

=============================================================================
\* Modification History
\* Created Thu Apr 07 09:06:06 YEKT 2022 by pervu
