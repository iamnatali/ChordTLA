---- MODULE MC ----
EXTENDS actor, TLC

\* CONSTANT definitions @modelParameterConstants:0bm
const_164930459337530000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:1m
const_164930459337631000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_164930459337632000 ==
LenStateConstraint
----
\* Constant expression definition @modelExpressionEval
const_expr_164930459337633000 == 
1
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_164930459337633000>>)
----

=============================================================================
\* Modification History
\* Created Thu Apr 07 09:09:53 YEKT 2022 by pervu
