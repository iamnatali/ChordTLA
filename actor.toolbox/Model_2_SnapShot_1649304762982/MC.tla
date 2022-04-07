---- MODULE MC ----
EXTENDS actor, TLC

\* CONSTANT definitions @modelParameterConstants:0bm
const_164930474474840000 == 
8
----

\* CONSTANT definitions @modelParameterConstants:1m
const_164930474474841000 == 
3
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_164930474474842000 ==
LenStateConstraint
----
\* Constant expression definition @modelExpressionEval
const_expr_164930474474843000 == 
1
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_164930474474843000>>)
----

=============================================================================
\* Modification History
\* Created Thu Apr 07 09:12:24 YEKT 2022 by pervu
