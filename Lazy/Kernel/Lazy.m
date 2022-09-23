Package["Wolfram`Lazy`"]

PackageExport["$LazyNoEntry"]
PackageExport["$LazyUp"]

PackageExport["$LazyCache"]
PackageExport["WithLazyCache"]

PackageExport["LazyQ"]
PackageExport["LazyValueQ"]
PackageScope["FlatQ"]
PackageScope["HoldQ"]
PackageScope["HoldFirstQ"]
PackageScope["FlatHoldQ"]
PackageScope["EvalFirst"]

PackageExport["LazyEval"]
PackageExport["LazyListEval"]
PackageExport["ArgEval"]
PackageExport["NormalLazy"]
PackageExport["LazyValueEval"]
PackageExport["ReleaseLazyValue"]

PackageExport["LazyValue"]

PackageExport["Lazy"]



$LazyNoEntry = True
$LazyUp = True
$LazyCache = False

WithLazyCache[expr_] := Block[{$LazyCache = True}, Evaluate[expr]]

SetAttributes[LazyValue, HoldAllComplete]

LazyValue /: l_LazyValue /; $LazyNoEntry && System`Private`HoldEntryQ[l] := System`Private`HoldSetNoEntry[l]

Scan[SetAttributes[#, Stub] &, {LazyValue, LazyList, Cons, LazyTree}]

LazyQ[l_] := MatchQ[Unevaluated[l], _LazyValue | _Cons | _LazyList | _LazyTree]

LazyValueQ[_LazyValue] ^:= True
LazyValueQ[___] := False

HoldQ[h_Symbol] := ContainsAny[Attributes[h], {HoldAll, HoldAllComplete}]
HoldQ[_] := False

HoldFirstQ[h_Symbol] := ContainsAny[Attributes[h], {HoldAll, HoldAllComplete, HoldFirst}]
HoldFirstQ[_] := False

FlatQ[h_Symbol] := MemberQ[Attributes[h], Flat]
FlatQ[_] := False

FlatHoldQ[h_Symbol] := With[{attrs = Attributes[h]}, MemberQ[attrs, Flat] && ContainsAny[attrs, {HoldAll, HoldAllComplete}]]
FlatHoldQ[_] := False


LazyEval[l_, _Integer ? NonPositive] := l
LazyEval[LazyValue[x_], 1] := x
LazyEval[LazyValue[x_], n : (_Integer ? Positive) | Infinity] := LazyEval[x, n - 1]
LazyEval[LazyTree[x_, l_], n_] := LazyTree[x, Evaluate[LazyEval[l, n]]]
LazyEval[h_[], _] /; HoldQ[h] := h[]
LazyEval[h_[x_], n : (_Integer ? Positive) | Infinity] /; HoldQ[h] && FlatQ[h] := h[Evaluate[LazyEval[x, n - 1]]]
LazyEval[h_[x__, l_], n : (_Integer ? Positive) | Infinity] /; HoldQ[h] := h[x, Evaluate[LazyEval[l, n - 1]]]
LazyEval[h_[l_], n : (_Integer ? Positive) | Infinity] /; HoldQ[h] := LazyEval[l, n - 1]
LazyEval[n : (_Integer ? NonNegative | Infinity) : 1] := Function[l, LazyEval[Unevaluated[l], n]]
LazyEval[l_] := LazyEval[l, 1]
LazyEval[l_, n_] := Nest[Replace[expr : h_Symbol[___] /; HoldQ[Unevaluated[h]] || Unevaluated[h] === LazyValue :> LazyEval[expr, 1]], Unevaluated[l], n]


LazyListEval[l_, _Integer ? NonPositive] := l
LazyListEval[LazyValue[l_], 1] := l
LazyListEval[LazyValue[l_], n_] := LazyListEval[l, n]
LazyListEval[LazyTree[x_, l_], n_] := LazyTree[x, Evaluate[LazyListEval[l, n]]]
LazyListEval[(h : LazyList | Cons)[], _] := h[]
LazyListEval[Cons[x_], n : (_Integer ? Positive) | Infinity] := Cons[Evaluate[LazyListEval[x, n - 1]]]
LazyListEval[(h : LazyList | Cons)[x__, l_], n : (_Integer ? Positive) | Infinity] := h[x, Evaluate[ReleaseLazyValue @ LazyListEval[l, n - 1]]]
LazyListEval[n : (_Integer ? NonNegative | Infinity) : 1] := Function[l, LazyListEval[Unevaluated[l], n]]
LazyListEval[l_] := LazyListEval[l, 1]
LazyListEval[l_, n_] := Nest[Replace[expr : _LazyList | _Cons | _LazyValue :> LazyListEval[expr, 1]], Unevaluated[l], n]


ArgEval[h_[x_, rest___]] /; HoldQ[h] :=
    With[{y = ReleaseLazyValue[x]}, If[MatchQ[Unevaluated[y], _Sequence] || LazyValueQ[x] || Unevaluated[x] === y, h[y, rest], ArgEval[h[y, rest]]]]
ArgEval[x___] := x
SetAttributes[ArgEval, SequenceHold]


EvalFirst[h_[LazyValue[x_] | x_, rest___]] := h[Evaluate[x], rest]


NormalLazy[l_] := Unevaluated[l] //. {t : _LazyTree :> LazyTreeSubtree[t], cons : _Cons | _LazyList :> LazyListToList[cons]}
NormalLazy[l_LazyValue] ^:= NormalLazy[ReleaseLazyValue[l]]


LazyValueEval[LazyValue[x_]] := With[{y = x}, If[$LazyCache, LazyValueEval[LazyValue[x]] = y]; y]
LazyValueEval[x_] := x
SetAttributes[LazyValueEval, {HoldFirst, SequenceHold}]


releaseLazyValue[l_LazyValue] := With[{y = LazyValueEval[l]}, releaseLazyValue[y]]
releaseLazyValue[x_] := x
SetAttributes[releaseLazyValue, {HoldFirst, SequenceHold}]
ReleaseLazyValue[x_] := Block[{$IterationLimit = Infinity}, releaseLazyValue[Evaluate[x]]]
SetAttributes[ReleaseLazyValue, {HoldFirst, SequenceHold}]


Normal[l_Cons] ^:= NormalLazy[l]
Normal[l_LazyList] ^:= NormalLazy[l]
Normal[l_LazyTree] ^:= NormalLazy[l]
Normal[l_LazyValue] ^:= NormalLazy[l]


LazyValue /: MakeBoxes[lazy : Verbatim[LazyValue][x_], _] := With[{boxes = ToBoxes @ DynamicModule[{expr},
        expr = Button[
            Tooltip[Framed["\[Ellipsis]"], HoldForm[DisableFormatting[x]]],
            expr = If[TrueQ[CurrentValue["OptionKey"]], Unevaluated[##] & [ReleaseLazyValue[lazy]], Unevaluated[##] &[LazyValueEval[lazy]]],
            Appearance -> None
        ];
        Dynamic[Block[{$LazyUp = False}, Replace[expr, {
            Verbatim[Unevaluated][seq : PatternSequence[_, __]] :> HoldForm[Sequence][seq],
            Verbatim[Unevaluated][y_] :> y
        }]]
        ],
        UndoTrackedVariables :> {expr}
    ]},
    InterpretationBox[boxes, lazy]
]



LazyValue /: (f : Except[ToBoxes])[left___, Verbatim[LazyValue][mid_], right___] /; $LazyUp && FreeQ[Unevaluated @ f, _LazyValue] := With[{
    i = Length @ Unevaluated @ {left} + 1
},
    LazyValue[f[left, mid, right]] /;
        With[{cond = ! (MatchQ[Unevaluated @ f, _Symbol] && MemberQ[Attributes[f], SequenceHold]) &&
        ! HoldPositionQ[Unevaluated[f[left, mid, right]], i]}, If[
            TrueQ[cond],
            (* Echo[Hold[DisableFormatting[f[left, LazyValue[mid], right]], Evaluate@Stack[]]]; *)
            True,
            False
        ]]
]


$Lazy = False;

Scan[symbol |->
	With[{lazySymbol = Symbol["Lazy" <> SymbolName[symbol]]},
        With[{rule = HoldPattern[symbol[args___] /; $Lazy] :> lazySymbol[args]},
            If[ !MemberQ[DownValues[symbol], Verbatim[rule]],
                Unprotect[symbol];
                DownValues[symbol] = Prepend[DownValues[symbol], rule];
                Protect[symbol]
            ]
        ]
	],
	{
		Range, Table, Array, ConstantArray, RandomInteger, Nest, NestWhile, NestList, NestWhileList, Position, Subdivide,
		NestTree
	}
]

Lazy[expr : Except[_Symbol]] := Block[{$Lazy = True}, expr]
SetAttributes[Lazy, HoldAll]

