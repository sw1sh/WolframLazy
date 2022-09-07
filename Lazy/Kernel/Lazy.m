Package["Wolfram`Lazy`"]

PackageScope["FlatQ"]
PackageScope["HoldQ"]
PackageScope["HoldFirstQ"]
PackageScope["FlatHoldQ"]
PackageScope["EvalFirst"]

PackageExport["LazyEval"]
PackageExport["LazyListEval"]
PackageExport["ArgEval"]
PackageExport["NormalLazy"]
PackageExport["ReleaseLazyValue"]

PackageExport["LazyValue"]
PackageExport["Thunk"]



SetAttributes[LazyValue, {HoldFirst, Flat, OneIdentity}]
SetAttributes[Thunk, {HoldFirst}]

Scan[SetAttributes[#, Stub] &, {LazyValue,Thunk, LazyList, Cons, LazyTree}]


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
LazyListEval[(h : LazyList | Cons)[x__, l_], n : (_Integer ? Positive) | Infinity] := h[x, Evaluate[LazyListEval[l, n - 1]]]
LazyListEval[n : (_Integer ? NonNegative | Infinity) : 1] := Function[l, LazyListEval[Unevaluated[l], n]]
LazyListEval[l_] := LazyListEval[l, 1]
LazyListEval[l_, n_] := Nest[Replace[expr : _LazyList | _Cons | _LazyValue :> LazyListEval[expr, 1]], Unevaluated[l], n]


ArgEval[h_[LazyValue[x_] | x_, rest___]] /; HoldQ[h] :=
    With[{y = x}, If[Unevaluated[x] === y, h[y, rest], ArgEval[h[y, rest]]]]
ArgEval[x___] := x
SetAttributes[ArgEval, SequenceHold]


EvalFirst[h_[LazyValue[x_] | x_, rest___]] := h[Evaluate[x], rest]


NormalLazy[l_] := Unevaluated[l] //. {LazyValue[x_] :> x, t : _LazyTree :> LazyTreeToTree[t], cons : _Cons | _LazyList :> LazyListToList[cons]}


releaseLazyValue[LazyValue[x_]] := releaseLazyValue[x]
releaseLazyValue[x_] := x

ReleaseLazyValue[x_] := Block[{$IterationLimit = Infinity}, releaseLazyValue[x]]


Normal[l_Cons] ^:= LazyListToList[l]
Normal[l_LazyList] ^:= LazyListToList[l]
Normal[t_LazyTree] ^:= LazyTreeToTree[t]
Normal[LazyValue[x_]] ^:= Normal[x]

Thunk[x_] := With[{z = ReleaseLazyValue[x]}, Thunk[x] = z; z]


Format[lazy : LazyValue[x_]] ^:= Interpretation[
    DynamicModule[{form},
        form = Button[
            Tooltip[Framed["\[Ellipsis]"], InputForm[lazy]], form = If[TrueQ[CurrentValue["OptionKey"]], ReleaseLazyValue[x], x],
            Appearance -> None
        ];
        Dynamic[form],
        UndoTrackedVariables :> {form}
    ],
    lazy
]


(* f_[left___, LazyValue[mid_], right___] := LazyValue[f[left, mid, right]] *)