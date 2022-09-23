Package["Wolfram`Lazy`"]

PackageExport["ConformToPattern"]



ApplyMissing[f_, g_, expr_] := If[MissingQ[expr], g /@ expr, f @ expr]
ApplyMissing[f_, g_][expr_] := ApplyMissing[f, g, Unevaluated[expr]]

HoldApply[f_, expr_] := Function[Null, f[Unevaluated[##]], HoldAll] @@ Unevaluated[expr]
HoldApply[f_][expr_] := HoldApply[f, Unevaluated[expr]]
SetAttributes[HoldApply, HoldRest]


ConformToPattern[expr_, Verbatim[HoldPattern][patt_], eval_] := ConformToPattern[Unevaluated[expr], Unevaluated[patt], eval]

ConformToPattern[expr_, patt_] := ConformToPattern[Unevaluated[expr], Unevaluated[patt], False]

ConformToPattern[head_[arg_, args___], head_[patt_, patts___], _] :=
	If[MatchQ[Unevaluated[arg], Unevaluated[patt]], HoldComplete[arg], ConformToPattern[arg, Unevaluated[patt], True]] //
		ApplyMissing[
			HoldApply[firstSubExpr |-> ApplyMissing[
				restSubExpr |-> Insert[restSubExpr, Unevaluated[firstSubExpr], {1, 1}],
				restSubExpr |-> Insert[restSubExpr, Unevaluated[firstSubExpr], {1, 1}],
				ConformToPattern[Unevaluated[head[args]], Unevaluated[head[patts]], True]
			]],
			HoldApply[firstSubExpr |-> Insert[HoldComplete[head[args]], Unevaluated[firstSubExpr], {1, 1}]]
		]

ConformToPattern[head1_[args___], (head2 : Except[Blank])[patts___], False] :=
	EchoEvaluation @ ConformToPattern[head1, Unevaluated[head2], True] //
		ApplyMissing[
			HoldApply[headExpr |-> ConformToPattern[Unevaluated[headExpr[args]], Unevaluated[headExpr[patts]], True]],
			HoldApply[headExpr |-> HoldComplete[headExpr[args]]]
		]


ConformToPattern[expr_, patt_, True] := If[MatchQ[Unevaluated[expr], Unevaluated[patt]], HoldComplete[expr], Missing[HoldComplete[expr]]]
ConformToPattern[expr_, patt_, False] := If[MatchQ[Unevaluated[expr], Unevaluated[patt]], HoldComplete[expr], ConformToPattern[expr, Unevaluated[patt], True]]


LazyExpression /: MatchQ[l_LazyExpression, patt_] := With[{expr = Unevaluated @@ l["Get"]},
	With[{conformExpr = ConformToPattern[expr, Unevaluated[patt]]},
		If[MissingQ[conformExpr], l["SetNoHead", First[conformExpr]]; l["Trigger"]; False, l["SetNoHead", conformExpr]; l["Trigger"]; True]
	]
]

LazyExpression /: Replace[l_LazyExpression, (head : Rule | RuleDelayed)[lhs_, rhs_]] := With[{expr = Unevaluated @@ l["Get"]},
	With[{conformExpr = ConformToPattern[expr, Unevaluated[lhs]]},
		If[	MissingQ[conformExpr],
			l["SetNoHead", First[conformExpr]]; l["Trigger"],
			l["SetNoHead", conformExpr]; l["Trigger"]; Replace[conformExpr, head[HoldComplete[lhs], rhs]]
		]
	]
]

