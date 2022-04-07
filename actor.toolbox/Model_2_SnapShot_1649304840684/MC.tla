---- MODULE MC ----
EXTENDS actor, TLC

\* CONSTANT definitions @modelParameterConstants:0bm
const_164930482192350000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:1m
const_164930482192351000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_164930482192352000 ==
LenStateConstraint
----
\* Constant expression definition @modelExpressionEval
const_expr_164930482192353000 == 
1
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_164930482192353000>>)
----

=============================================================================
\* Modification History
\* Created Thu Apr 07 09:13:41 YEKT 2022 by pervu
