Package["Wolfram`Lazy`"]

PackageExport["MapValues"]
PackageExport["UnheldSubexpressions"]
PackageExport["ExtractValues"]
PackageExport["ExtractPositionValues"]
PackageExport["MultiEvaluate"]



MapValues[f_, a : {(_Rule | _RuleDelayed)...} | _Association] :=
	If[AssociationQ[a], Association, Identity] @ MapThread[With[{v = Unevaluated @@ #2},
		With[{w = Unevaluated @@ HoldComplete[Evaluate @ f[v]]}, #1 :> w]] &, {Keys[a], Values[a, HoldComplete]}
	]
MapValues[f_][a_] := MapValues[f, a]


Options[UnheldSubexpressions] = Options[ResourceFunction["SubexpressionPositions"]]

UnheldSubexpressions[expr_, args___, Longest[opts : OptionsPattern[]]] := ResourceFunction["SubexpressionPositions"][Unevaluated @ expr, args, opts,
	"OuterMatch" -> Except[
		((sym_Symbol[___] -> {__}) /; ContainsAny[Attributes[sym], {HoldAll, HoldAllComplete}]) |
		((sym_Symbol[___] -> {1, ___}) /; ContainsAny[Attributes[sym], {HoldFirst}]) |
		((sym_Symbol[___] -> {p_, ___} /; p > 1) /; ContainsAny[Attributes[sym], {HoldRest}])],
	"OuterMode" -> All
]

ExtractOwnValues[sym_Symbol] := OwnValues[sym]
ExtractOwnValues[___] := {}

ExtractDownValues[head_Symbol[args___]] := Cases[DownValues[head], _[lhs_, _] /; MatchQ[Unevaluated[head[args]], lhs]]
ExtractDownValues[___] := {}

ExtractUpValues[head_[args___]] := Catenate[Function[arg,
	Cases[
		With[{h = Head @ Unevaluated @ arg}, If[MatchQ[Unevaluated @ h, _Symbol], UpValues[h], {}]],
		_[lhs_, _] /; MatchQ[Unevaluated[head[args]], lhs]],
	HoldAll
    ] /@ Unevaluated[{args}]
]
ExtractUpValues[___] := {}

ExtractHead[expr_, h_] := With[{head = Head[Unevaluated @ expr, Hold]}, If[MatchQ[head, Hold[_Symbol]], h @@ head, ExtractHead @@ Append[head, h]]]
ExtractHead[expr_] := With[{head = Head[Unevaluated @ expr, Hold]}, If[MatchQ[head, Hold[_Symbol]], ReleaseHold @ head, ExtractHead @@ head]]

ExtractSubValues[expr_] := With[{sym = ExtractHead[Unevaluated[expr], Hold]}, Cases[SubValues @@ sym, _[lhs_, _] /; MatchQ[Unevaluated[expr], lhs]]]


QuietCheck[expr_, def_ : {}, msg_ : Unevaluated[General::readp]] := Quiet[Check[expr, def, msg], msg]
SetAttributes[QuietCheck, HoldFirst]

ExtractValues[expr_] := DeleteCases[{}] @ <|
	"Sub" -> QuietCheck[ExtractSubValues[Unevaluated[expr]]],
	"Own" -> QuietCheck[ExtractOwnValues[Unevaluated[expr]]],
	"Up" -> QuietCheck[ExtractUpValues[Unevaluated[expr]]],
	"Down" -> QuietCheck[ExtractDownValues[Unevaluated[expr]]]
|>

Options[ExtractPositionValues] = Options[UnheldSubexpressions]
ExtractPositionValues[expr_, args___, Longest[opts : OptionsPattern[]]] := Association @ Replace[
    Normal @ DeleteCases[None] @ MapValues[
        Function[subExpr, Replace[ExtractValues[Unevaluated[subExpr]] :> subExpr, (<||> :> _) -> None], HoldAll],
        UnheldSubexpressions[Unevaluated[expr], args, opts]
    ],
    (pos_ :> values_ :> subExpr_) :> {pos, values} :> subExpr,
    {1}
]

Options[MultiEvaluate] = Options[ExtractPositionValues]
MultiEvaluate[expr_, args___, Longest[opts : OptionsPattern[]]] :=
	Association @ Map[Replace[({pos_, values_} :> holdSubExpr_) :> {pos, holdSubExpr} ->
		Association @ KeyValueMap[{type, rules} |-> type -> Association @ Map[rule |->
			rule -> Replace[rule, _[lhs_, rhs_] :> Block[{
					patts = Union @ Cases[Unevaluated[lhs], Verbatim[Pattern][name_, _] :> Hold[name], All, Heads -> True]
				},
				With[{bindings = Map[
					MapThread[With[{newRhs = Unevaluated @@ #2}, #1 :> newRhs] &, {HoldPattern @@@ patts, #}] &,
					ReplaceList[holdSubExpr, HoldForm[lhs] -> patts]
				]},
					Association @ Map[# -> With[{
						newSubExpr = Unevaluated @@ (Hold[rhs] /. #)
					},
						ReplacePart[HoldForm[expr], Prepend[pos, 1] :> newSubExpr]
					] &,
						bindings
					]
				]
				]
			],
			rules
			],
			values
		]],
		Normal[HoldForm /@ ExtractPositionValues[Unevaluated[expr], args, opts]]
	]
