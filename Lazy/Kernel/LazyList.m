Package["Wolfram`Lazy`"]

PackageExport["Cons"]
PackageExport["LazyList"]

PackageExport["LazyListQ"]

PackageExport["ConsForm"]
PackageExport["ConsLast"]
PackageExport["LazyListForm"]
PackageExport["LazyListToList"]

PackageExport["LazyLength"]
PackageExport["LazyAllTrue"]
PackageExport["LazyAnyTrue"]

PackageExport["LazyMap"]
PackageExport["LazyMapIndexed"]
PackageExport["LazySelect"]
PackageExport["LazyJoin"]
PackageExport["LazyAppend"]
PackageExport["LazyPrepend"]
PackageExport["LazyCatenate"]
PackageExport["LazyFirst"]
PackageExport["LazyRest"]
PackageExport["LazyTake"]
PackageExport["LazyDrop"]
PackageExport["LazyTakeDrop"]
PackageExport["LazyTakeWhile"]
PackageExport["LazyDropWhile"]

PackageExport["LazyFold"]
PackageExport["LazyFoldList"]
PackageExport["LazyFoldRight"]
PackageExport["LazyFoldRightList"]
PackageExport["LazyMapThread"]

PackageExport["ToLazyList"]
PackageExport["LazyNest"]
PackageExport["LazyNestWhile"]
PackageExport["LazyNestList"]
PackageExport["LazyNestWhileList"]
PackageExport["LazyRange"]
PackageExport["LazyTable"]
PackageExport["LazyClone"]
PackageExport["LazyRepeat"]
PackageExport["LazySplits"]
PackageExport["LazySplitsReverse"]
PackageExport["LazyPosition"]
PackageExport["LazySubsets"]
PackageExport["LazyTuples"]
PackageExport["LazyPermutations"]
PackageExport["LazySubdivide"]
PackageExport["LazyArray"]
PackageExport["LazyConstantArray"]



SetAttributes[Cons, {HoldAll, Flat, OneIdentity}]
SetAttributes[LazyList, {HoldAll}]


LazyListQ[l_] := MatchQ[Unevaluated[l], _Cons | _LazyList]

LazyList[x_] := ToLazyList[Unevaluated[x]]
LazyList[Nothing, l_] := l

(* Functions *)

LazyMap[f_, h_[]] := h[]
LazyMap[f_, h_[LazyValue[x_] | x_, l___]] /; FlatQ[h] := h[f[x], LazyMap[f, ArgEval[h[l]]]]
LazyMap[f_, h_[LazyValue[x_] | x_, l_]] := h[f[x], LazyMap[f, l]]
LazyMap[f_, h_[l_]] := LazyValue[LazyMap[f, l]]
LazyMap[f_][l_] := LazyMap[f, l]


LazyMapIndexed[f_, l_] := LazyMapThread[f, LazyList[l, LazyList[LazyMap[List, LazyRange[]], LazyList[]]]]


LazySelect[h_[], _] := h[]
LazySelect[h_[LazyValue[x_] | x_, l___], crit_] /; FlatQ[h] :=
    With[{z = x}, If[TrueQ[crit[z]], h[z, LazySelect[ArgEval[h[l]], crit]], LazyValue @ LazySelect[ArgEval[h[l]], crit]]]
LazySelect[h_[LazyValue[x_] | x_, l_], crit_] := With[{z = x}, If[TrueQ[crit[z]], h[z, LazySelect[l, crit]], LazyValue @ LazySelect[l, crit]]]
LazySelect[h_[l_], crit_] := LazyValue @ LazySelect[l, crit]
LazySelect[crit_][l_] := LazySelect[l, crit]


LazyFirst[h_[x_, ___], ___] /; FlatQ[h] := x
LazyFirst[h_[x_, _], ___] := x
LazyFirst[_[l_], def___] := LazyValue[LazyFirst[l, def]]
LazyFirst[_[], def_] := def
LazyFirst[l : _[]] /; Message[First::nofirst, l] := Null


LazyRest[h_[_, l___], ___] /; FlatQ[h] := h[l]
LazyRest[h_[_, l_], ___] := l
LazyRest[_[l_], def___] := LazyValue[LazyRest[l, def]]
LazyRest[_[], def_] := def


LazyDrop[h_[], _] := h[]
LazyDrop[h_[_, l___], n_] /; FlatQ[h] := If[n <= 0, h[], LazyValue[LazyDrop[ArgEval[h[l]], n - 1]]]
LazyDrop[h_[x_, l_], n_] := If[n <= 0, h[x, l], LazyValue[LazyDrop[l, n - 1]]]
LazyDrop[h_[l_], n_] := LazyValue[LazyDrop[l, n]]
LazyDrop[n_][l_] := LazyDrop[l, n]


LazyTake[h_[], _] := h[]
LazyTake[h_[x_, l___], n_] /; FlatQ[h] := If[n <= 0, h[], h[x, LazyTake[ArgEval[h[l]], n - 1]]]
LazyTake[h_[x_, l_], n_] := If[n <= 0, h[], h[x, LazyTake[l, n - 1]]]
LazyTake[h_[l_], n_] := LazyValue[LazyTake[l, n]]
LazyTake[n_][l_] := LazyTake[l, n]


LazyTakeDrop[h_[], _] := {h[], h[]}
LazyTakeDrop[h_[x_, l___], n_] /; FlatQ[h] := If[n <= 0, {h[], h[x, l]}, Replace[LazyTakeDrop[ArgEval[h[l]], n - 1], {t_, d_} :> {h[x, t], d}]]
LazyTakeDrop[h_[x_, l_], n_] := {LazyTake[h[x, l], n], LazyDrop[h[x, l], n]}
LazyTakeDrop[h_[l_], n_] := LazyValue[LazyTakeDrop[l, n]]
LazyTakeDrop[n_][l_] := LazyTakeDrop[l, n]


LazyDropWhile[h_[], _] := h[]
LazyDropWhile[h_[LazyValue[x_] | x_, l___], crit_] /; FlatQ[h] := If[TrueQ[crit[x]], LazyValue[LazyDropWhile[ArgEval[h[l]], crit]], h[]]
LazyDropWhile[h_[LazyValue[x_] | x_, l_], crit_] := If[TrueQ[crit[x]], LazyValue[LazyDropWhile[l, crit]], h[]]
LazyDropWhile[h_[l_], crit_] := LazyValue[LazyDropWhile[l, crit]]
LazyDropWhile[crit_][l_] := LazyDropWhile[l, crit]


LazyTakeWhile[h_[], _] := h[]
LazyTakeWhile[h_[LazyValue[x_] | x_, l___], crit_] /; FlatQ[h] := If[TrueQ[crit[x]], h[x, LazyTakeWhile[ArgEval[h[l]], crit]], h[]]
LazyTakeWhile[h_[LazyValue[x_] | x_, l_], crit_] := If[TrueQ[crit[x]], h[x, LazyTakeWhile[l, crit]], h[]]
LazyTakeWhile[h_[l_], crit_] := LazyValue[LazyTakeWhile[l, crit]]
LazyTakeWhile[crit_][l_] := LazyTakeWhile[l, crit]


LazyAppend[h_[], x_] := h[x, h[]]
LazyAppend[h_[x_, l___], y_] /; FlatQ[h]:= h[x, LazyAppend[ArgEval[h[l]], y]]
LazyAppend[h_[x_, l_], y_] := h[x, LazyAppend[l, y]]
LazyAppend[h_[l_], x_] := LazyValue @ LazyAppend[l, x]
LazyAppend[x_][l_] := LazyAppend[l, x]


LazyPrepend[h_[], x_] := h[x, h[]]
LazyPrepend[h_[x_, l___], y_] /; FlatQ[h] := h[y, x, l]
LazyPrepend[h_[x_, l_], y_] := h[y, h[x, l]]
LazyPrepend[h_[l_], x_] := LazyValue @ LazyPrepend[l, x]
LazyPrepend[x_][l_] := LazyPrepend[l, x]


LazyReverse[h_[x_, l___]] /; FlatQ[h] := LazyValue @ LazyAppend[LazyReverse[ArgEval[h[l]]], x]
LazyReverse[h_[x_, l_]] := LazyValue @ LazyAppend[LazyReverse[l], x]
LazyReverse[h_[l_]] := LazyValue @ LazyReverse[l]


LazyJoin[LazyValue[x_] | x_] := x
LazyJoin[h_[], rest__] := LazyJoin[rest]
LazyJoin[h_[x__, l_], rest__] /; FlatQ[h] := h[x, LazyJoin[l, rest]]
LazyJoin[h_[LazyValue[x_] | x_, l_], rest__] := h[x, LazyJoin[l, rest]]
LazyJoin[h_[l_], rest__] := LazyValue[LazyJoin[l, rest]]


LazyCatenate[h_[]] := h[]
LazyCatenate[h_[h_[LazyValue[x_] | x_, l___], rest___]] /; FlatQ[h] := h[x, LazyJoin[h[l], LazyCatenate[h[rest]]]]
LazyCatenate[h_[LazyList[LazyValue[x_] | x_, l_], rest___]] /; FlatQ[h] := h[x, LazyJoin[LazyCatenate[h[l]], LazyCatenate[h[rest]]]]
LazyCatenate[h_[h_[LazyValue[x_] | x_, l_], rest_]] := h[x, LazyJoin[l, LazyCatenate[rest]]]
LazyCatenate[h_[h_[], rest_]] :=  LazyCatenate[rest]
LazyCatenate[h_[h_[l_], rest__]] := LazyValue[LazyCatenate[h[l, rest]]]
LazyCatenate[LazyValue[l_]] := LazyValue @ LazyCatenate[l]
LazyCatenate[l_] := With[{r = ArgEval[l]}, If[Unevaluated[l] === r, r, LazyCatenate[r]]]


LazyFold[f_, x_, h_[]] := x
LazyFold[f_, h_[x_, l___]] /; FlatQ[h] := LazyFold[f, x, ArgEval[h[l]]]
LazyFold[f_, x_, h_[y_, l___]] /; FlatQ[h] := LazyValue @ LazyFold[f, f[x, y], ArgEval[h[l]]]
LazyFold[f_, h_[x_, l_]] := LazyFold[f, x, l]
LazyFold[f_, x_, h_[y_, l_]] := LazyValue @ LazyFold[f, f[x, y], l]
LazyFold[f_, h_[l_]] := LazyValue[LazyFold[f, l]]
LazyFold[f_, x_, h_[l_]] := LazyValue[LazyFold[f, x, l]]
LazyFold[f_][l_] := LazyFold[f, l]


LazyFoldRight[f_, x_, h_[]] := x
LazyFoldRight[f_, h_[x_, l___]] /; FlatQ[h] := f[LazyFoldRight[f, ArgEval[h[l]]], x]
LazyFoldRight[f_, x_, h_[y_, l___]] /; FlatQ[h] := f[y, LazyFoldRight[f, x, ArgEval[h[l]]]]
LazyFoldRight[f_, h_[x_, l_]] := f[x, LazyFoldRight[f, l]]
LazyFoldRight[f_, x_, h_[y_, l_]] := f[y, LazyFoldRight[f, x, l]]
LazyFoldRight[f_, h_[l_]] := LazyValue[LazyFoldRight[f, l]]
LazyFoldRight[f_, x_, h_[l_]] := LazyValue[LazyFoldRight[f, x, l]]
LazyFoldRight[f_][l_] := LazyFoldRight[f, l]


LazyFoldList[_, x_, h_[]] := h[x, h[]]
LazyFoldList[f_, h_[x_, l___]] /; FlatQ[h] := LazyFoldList[f, x, ArgEval[h[l]]]
LazyFoldList[f_, x_, h_[y_, l___]] /; FlatQ[h] := With[{z = f[x, y]}, h[x, LazyFoldList[f, z, ArgEval[h[l]]]]]
LazyFoldList[f_, x_, h_[y_, l_]] := With[{z = f[x, y]}, h[x, LazyFoldList[f, z, l]]]
LazyFoldList[f_, h_[x_, l_]] := LazyFoldList[f, x, l]
LazyFoldList[f_, h_[l_]] := LazyValue[LazyFoldList[f, l]]
LazyFoldList[f_, x_, h_[l_]] := LazyValue[LazyFoldList[f, x, l]]
LazyFoldList[f_][l_] := LazyFoldList[f, l]


LazyFoldRightList[_, x_, h_[]] := h[x, h[]]
LazyFoldRightList[f_, x_, r : h_[___]] := LazyFoldList[ReverseApplied[f], x, LazyReverse[r]]
LazyFoldRightList[f_, r : h_[___]] := LazyFoldList[ReverseApplied[f], LazyReverse[r]]
LazyFoldRightList[f_, h_[l_]] := LazyValue[LazyFoldRightList[f, l]]
LazyFoldRightList[f_, x_, h_[l_]] := LazyValue[LazyFoldRightList[f, x, l]]
LazyFoldRightList[f_][l_] := LazyFoldRightList[f, l]


LazyMapThread[f_, l_List] :=
    If[ l === {},
        LazyList[],
        With[{xs = Quiet[Check[Map[ReleaseLazyValue @ LazyFirst[#] &, l], {}, First::nofirst], First::nofirst]},
            If[ Length[xs] < Length[l],
                LazyList[],
                LazyList[f @@ xs, LazyMapThread[f, Map[LazyRest, l]]]
            ]
        ]
    ]

LazyMapThread[_, h_[]] := h[]
LazyMapThread[f_, l : h_[__]] := With[{r = LazyTakeWhile[l, MatchQ[Verbatim[h][__]]]},
    If[ r === h[],
        h[],
        h[LazyFold[f, LazyMap[LazyFirst, r]], LazyMapThread[f, LazyMap[LazyRest, r]]]
    ]
]


(* Queries *)

LazyLength[_[], n_ : 0] := n
LazyLength[h_[_, l___], n_ : 0] /; FlatQ[h] := LazyValue[LazyLength[ArgEval[h[l]], n + 1]]
LazyLength[h_[_, l_], n_ : 0] := LazyValue[LazyLength[l, n + 1]]
LazyLength[h_[l_], n_ : 0] := LazyValue[LazyLength[l, n]]


LazyAllTrue[h_[], _] := True
LazyAllTrue[h_[LazyValue[x_] | x_, l___], test_] /; FlatQ[h] := If[test[x], LazyAllTrue[ArgEval[h[l]], test], False]
LazyAllTrue[h_[LazyValue[x_] | x_, l_], test_] := If[test[x], LazyAllTrue[l, test], False]
LazyAllTrue[h_[l_], test_] := LazyValue[LazyAllTrue[l, test]]


LazyAnyTrue[h_[], _] := False
LazyAnyTrue[h_[LazyValue[x_] | x_, l___], test_] /; FlatQ[h] := If[test[x], True, LazyAnyTrue[h[l], test]]
LazyAnyTrue[h_[LazyValue[x_] | x_, l_], test_] := If[test[x], True, LazyAnyTrue[l, test]]
LazyAnyTrue[h_[l_], test_] := LazyValue[LazyAnyTrue[l, test]]


(* Generators *)

ToLazyList[l : h_[___], h_Symbol : LazyList] := l
ToLazyList[(g : Cons | List)[x_, rest___], h_Symbol : LazyList] := h[x, ToLazyList[g[rest], h]]
ToLazyList[Verbatim[LazyList][x_, rest_], h_Symbol : LazyList] := h[x, ToLazyList[rest, h]]
ToLazyList[(List | Cons | LazyList)[], h_Symbol : LazyList] := h[]
ToLazyList[LazyValue[x_], h_Symbol : LazyList]:= LazyValue[ToLazyList[x, h]]
ToLazyList[x_, h_Symbol : LazyList] := h[x, h[]]


LazyNest[f_, x_, n : _Integer ? NonNegative | Infinity : Infinity] :=
    If[n <= 0, x, LazyValue @ LazyNest[f, f[x], n - 1]]

lazyNestWhile[f_, xs_List, crit_, {mmin : _Integer ? Positive, m : _Integer ? Positive | Infinity : 1}, max : _Integer | Infinity : Infinity, n : _Integer | Infinity : 0] :=
    With[{newMax = If[max <= 0, max - 1, If[Length[xs] < mmin || TrueQ[crit @@ Drop[xs, UpTo[Max[Length[xs] - m, 0]]]], max - 1, -1]]},
        If[ max > 0 || n > 0,
            LazyValue @ lazyNestWhile[f, Append[Drop[xs, UpTo[Max[Length[xs] - Max[m, -n + 1] + 1, 0]]], f[Last[xs]]], crit, {mmin, m}, newMax, If[newMax < 0 && n > 0, n - 1, n]],
            xs[[-1 + n]]
        ]
    ]
LazyNestWhile[f_, x_, crit_, m : _Integer ? Positive | All | {_Integer ? Positive, _Integer ? Positive | Infinity} : 1, max : _Integer ? NonNegative | Infinity : Infinity, n : _Integer | Infinity : 0] :=
    lazyNestWhile[f, {x}, crit, Replace[m, {All -> {1, Infinity}, k_Integer :> {k, k}}], max, n]

lazyNestWhileList[f_, xs_List, crit_, {mmin : _Integer ? Positive, m : _Integer ? Positive | Infinity : 1}, max : _Integer | Infinity : Infinity, n : _Integer | Infinity : 0, h_Symbol : LazyList] :=
With[{newMax = If[max <= 0, max - 1, If[Length[xs] < mmin || TrueQ[crit @@ Drop[xs, UpTo[Max[Length[xs] - m, 0]]]], max - 1, -1]], y = f[Last[xs]]},
    If[ max > 0 || n > 0,
        h[y, lazyNestWhileList[f, Append[Drop[xs, UpTo[Max[Length[xs] - Max[m, -n + 1] + 1, 0]]], y], crit, {mmin, m}, newMax, If[newMax < 0 && n > 0, n - 1, n], h]],
        h[y, h[]]
    ]
]
LazyNestWhileList[f_, x_, crit_, m : _Integer ? Positive | All | {_Integer ? Positive, _Integer ? Positive | Infinity} : 1, max : _Integer ? NonNegative | Infinity : Infinity, n : _Integer | Infinity : 0, h_Symbol : LazyList] :=
    LazyTake[h[x, lazyNestWhileList[f, {x}, crit, Replace[m, {All -> {1, Infinity}, k_Integer :> {k, k}}], max, n, h]], Max[max + n + 1, 0]]

LazyNestList[f_, x_, n : _Integer ? NonNegative | Infinity : Infinity, h_Symbol : LazyList] :=
    If[n <= 0, h[x, h[]], h[x, LazyNestList[f, f[x], n - 1, h]]]


LazyRange[from : _ ? NumericQ, to : _ ? NumericQ | Infinity, step : _ ? NumericQ : 1, h_Symbol] := If[from > to && step > 0 || from < to && step < 0, h[],
    With[{next = from + step}, h[from, LazyRange[next, to, step, h]]]
]
LazyRange[from : _ ? NumericQ, to : _ ? NumericQ | Infinity, step : _ ? NumericQ : 1] := LazyRange[from, to, step, LazyList]
LazyRange[to  : _ ? NumericQ | Infinity, h_Symbol : LazyList] := LazyRange[1, to, h]
LazyRange[h_Symbol : LazyList] := LazyRange[Infinity, h]

SetAttributes[LazyTable, HoldFirst]
LazyTable[expr_, {var_Symbol, to_}, h_Symbol : LazyList] := LazyTable[expr, {var, 1, to}, h]
LazyTable[expr_, var_Symbol, h_Symbol : LazyList] := LazyTable[expr, {var, Infinity}, h]
LazyTable[expr_, {var_Symbol, from_, to_}, h_Symbol : LazyList] := If[
    from > to,
    h[],
    With[{
        next = from + 1
    },
        h[Block[{var = from}, expr], LazyTable[expr, {var, next, to}, h]]
    ]
]


LazyRepeat[x_, h_Symbol : LazyList] := h[x, LazyRepeat[x, h]]
SetAttributes[LazyRepeat, HoldFirst]


LazyClone[h_[]] := h[]
LazyClone[l_] := LazyJoin[l, LazyValue @ LazyClone[l]]


LazySplits[list : _[___], 1, h_Symbol : LazyList] := h[LazyList[list, LazyList[]], h[]]
LazySplits[list : _[___], n_Integer ? Positive, h_Symbol : LazyList] :=
	LazyCatenate @ LazyMap[
		split |-> With[{first = LazyFirst[split], rest = LazyRest[split]},
			LazyMap[LazyJoin[ToLazyList[TakeDrop[first, #]], rest] &, LazyRange[0, Length[first]]]
		],
		LazySplits[Unevaluated[list], n - 1, h]
	]
LazySplits[list : _[___], h_Symbol : LazyList] := LazySplits[Unevaluated[list], 2, h]

LazySplitsReverse[list : _[___], 1, h_Symbol : LazyList] := h[LazyList[list, LazyList[]], h[]]
LazySplitsReverse[list : _[___], n_Integer ? Positive, h_Symbol : LazyList] :=
	LazyCatenate @ LazyMap[
		split |-> With[{first = LazyFirst[split], rest = LazyRest[split]},
			With[{len = Length[first]}, LazyMap[LazyJoin[ToLazyList[TakeDrop[first, len - #]], rest] &, LazyRange[0, len]]]
		],
		LazySplitsReverse[Unevaluated[list], n - 1, h]
	]
LazySplitsReverse[list : _[___], h_Symbol : LazyList] := LazySplitsReverse[Unevaluated[list], 2, h]


LazySubsets[h_[]] := h[h[], h[]]
LazySubsets[h_[x_, l_]] :=
	h[h[], LazyJoin[LazyMap[LazyPrepend[#, x] &, LazySubsets[l]], LazyValue @ LazyRest @ LazySubsets[l]]]


LazyTuples[{x_}] := LazyMap[List, ToLazyList[x]]
LazyTuples[{xs__, x_}] := LazyCatenate @ LazyMap[t |-> LazyMap[Join[t, #] &, LazyTuples[{x}]], LazyTuples[{xs}]]


LazyPermutations[xs_] := With[{len = Length[xs]}, LazyMap[xs[[ ResourceFunction["PermutationFromIndex"][#, len] ]] &, If[len > 0, LazyRange[len !], LazyList[]]]]


Options[lazyPosition] = Options[Position]
lazyPosition[expr : head_[args___], patt_, pos_, opts : OptionsPattern[]] := LazyJoin[
    If[TrueQ[OptionValue[Heads]], lazyPosition[Unevaluated[head], patt, Prepend[pos, 0], opts], LazyList[]],
    If[
        MatchQ[Unevaluated[expr], patt],
        LazyList[pos, LazyCatenate @ LazyMapIndexed[Function[{arg, p}, lazyPosition[Unevaluated[arg], patt, Join[pos, p], opts], HoldFirst], ToLazyList @ Unevaluated[{args}]]],
        LazyCatenate @ LazyMapIndexed[Function[{arg, p}, lazyPosition[Unevaluated[arg], patt, Join[pos, p]], HoldFirst], ToLazyList @ Unevaluated[{args}]]
    ]
]
lazyPosition[expr_, patt_, pos_, OptionsPattern[]] := If[MatchQ[Unevaluated[expr], patt], LazyList[pos, LazyList[]], LazyList[]]

Options[LazyPosition] = Options[Position]
LazyPosition[expr_, patt_, opts : OptionsPattern[]] := lazyPosition[Unevaluated[expr], patt, {}, opts]
LazyPosition[expr_] := LazyPosition[Unevaluated[expr], _]


LazySubdivide[min_, max_, n : _Integer ? NonNegative] := min + (max - min)/n LazyRange[0, n]
LazySubdivide[n : _Integer ? NonNegative] := LazySubdivide[0, 1, n]
LazySubdivide[max_, n : _Integer ? NonNegative] := LazySubdivide[0, max, n]

LazyRests[l_] := LazyNestList[LazyRest, l]


LazyArray[f_, LazyList[], LazyList[]] := f[]
LazyArray[f_, ns_LazyList, rs_LazyList] :=
	Map[x |-> LazyArray[f[x, ##] &, Rest[ns], Rest[rs]], If[ListQ[#2], LazySubdivide[Sequence @@ Take[#2, UpTo[2]], #1 - 1], #2 + LazyRange[0, #1 - 1]] &[First[ns], First[rs]]]
LazyArray[f_, ns : {(_Integer ? NonNegative | Infinity)...}, rs_List] /; Length[ns] == Length[rs] || Message[Array::plen, ns, rs] :=
	LazyArray[f, LazyList[ns], LazyList[rs]]
LazyArray[f_, n : _Integer ? NonNegative | Infinity : Infinity, r_ : 1] := LazyArray[f, {n}, {r}]


LazyConstantArray[c_, LazyList[]] := c
LazyConstantArray[c_, ns_LazyList] := Map[x |-> LazyConstantArray[c, Rest[ns]], LazyRange[First[ns]]]
LazyConstantArray[c_, ns_] := LazyConstantArray[c, LazyList[ns]]


(* Listable *)

Cons /: f_Symbol[left___, cons__Cons, right___] /; MemberQ[Attributes[f], Listable] := LazyMap[f[left, #, right] &, cons]
LazyList /: f_Symbol[left___, cons__LazyList, right___] /; MemberQ[Attributes[f], Listable] := LazyMap[f[left, #, right] &, cons]


(* Formatting *)

LazyListToList[LazyValue[x_]] := If[Length[Stack[]] >= $RecursionLimit - 2, x, LazyListToList[x]]
LazyListToList[cons : _Cons | _LazyList | ((head : Except[LazyTree | Hold | HoldComplete, _Symbol])[___] /; HoldQ[head])] := Block[{
    x = cons, l = {}, recurseQ = MatchQ[Head[cons], LazyValue | Cons | LazyList]
},
    If[Length[Stack[]] >= $RecursionLimit - 2, Return[{}]];
    CheckAbort[
        While[
            MatchQ[x, _Cons | _LazyList | _head],
             Replace[ArgEval[x], {
                _[] :> Break[],
                h_[y__, z_] /; FlatQ[h] :> (
                    l = Join[l, If[recurseQ, Map[LazyListToList], Identity] @ {y}];
                    x = h[Evaluate[z]]
                ),
                h_[y_] /; FlatQ[h] :> (
                    l = Append[l, If[recurseQ, LazyListToList, Identity] @ y];
                    Break[]
                ),
                _[y_, z_] :> (l = Append[l, If[recurseQ, LazyListToList, Identity] @ y]; x = z),
                _[z_] :> (x = z)
             }];
        ],
        Null
    ];
    If[ !recurseQ,
        l = Head[cons] @@ l
    ];
    l
]
LazyListToList[x_] := x


(* ConsForm[h_[x___, l : h_[___]]] /; FlatQ[h] := {x, Splice[ConsForm[Unevaluated[l]]]} *)
ConsForm[Cons[x_]] := {x}
ConsForm[Cons[x___, l_]] := {x}
ConsForm[LazyList[x_, l : h_[___]]] := {x, Splice[ConsForm[Unevaluated[l]]]}
ConsForm[LazyList[x_, l_]] := {x}
ConsForm[(Cons | LazyList)[]] := {}
ConsForm[_] := {}

ConsLast[Cons[___, l_]] := h[l]
ConsLast[LazyList[___, l_]] := ConsLast[Unevaluated[l]]
ConsLast[(h : Cons | LazyList)[]] := h[]
ConsLast[x_] := x


LazyListForm[cons : _[LazyValue[x_] | x_, _[]]] := Tooltip[{x}, InputForm[cons]]

LazyListForm[cons : _[]] := Tooltip[{}, InputForm[cons]]
LazyListForm[cons : _[Longest[x__], LazyValue[l_] | l_]] := DynamicModule[{values = {x}, placeholder = Null, new, rest = LazyValue[l]},
    rest = FixedPoint[Replace[{
            LazyValue[LazyList[y_, next_]] :> (
                AppendTo[values, y];
                LazyValue[next]
            )
        }],
        rest
    ];
    new = Hold[placeholder];
    Tooltip[
        Row[{"{", Row[{
            Row[values, ","],
            Dynamic @ If[placeholder === Null, Row[{}], placeholder],
            Dynamic @ If[ValueQ[rest], Row[{", ", Tooltip[
                Button[
                    Framed["\[Ellipsis]"],
                    DynamicModule[{newElement, newPlaceholder = Null},
                        Replace[rest, {
                            h_[LazyValue[y_] | y_, next___] /; HoldQ[h] && FlatQ[h] :> (
                                newElement = y;
                                rest = ArgEval[h[next]];
                            ),
                            h_[LazyValue[y_] | y_, next_] /; HoldQ[h] :> (
                                newElement = y;
                                rest = next;
                            ),
                            h_[next_] /; HoldQ[h]  :> (rest = next),
                            LazyValue[next_] :> (rest = next),
                            _[] :> Clear[rest],
                            y_ :> (newElement = y; Clear[rest])
                        }];
                        If[ ValueQ[newElement],
                            Function[Null, # :=
                                Row[{", ", newElement, Dynamic @ If[newPlaceholder === Null, Row[{}], newPlaceholder]}],
                                HoldFirst
                            ] @@ new;
                            new = Hold[newPlaceholder]
                        ]
                    ],
                    Appearance -> None
                ],
                InputForm[rest]
            ]}], Row[{}]]}
            ],
            "}"
        }],
        InputForm[cons]
    ]
]
LazyListForm[cons : h_[LazyValue[x_] | x_]] /; HoldQ[h] && FlatQ[h] := Tooltip[{x}, InputForm[cons]]
LazyListForm[h_[LazyValue[x_] | x_]] /; HoldQ[h] := Format[LazyValue[x]]


l_Cons["DynamicList"] := LazyListForm[l]
l_LazyList["DynamicList"] := LazyListForm[l]

MakeBoxes[l_LazyList, form_] ^:= With[{
    icon = ""
},
    BoxForm`ArrangeSummaryBox[
        "LazyList",
        l,
        icon,
        {{BoxForm`SummaryItem[{l["DynamicList"]}]}},
        {{}},
        form,
		"Interpretable" -> Automatic
	]
]

MakeBoxes[l_Cons, form_] ^:= With[{
    icon = ""
},
    BoxForm`ArrangeSummaryBox[
        "LazyList",
        l,
        icon,
        {{BoxForm`SummaryItem[{l["DynamicList"]}]}},
        {{}},
        form,
		"Interpretable" -> Automatic
	]
]

(* UpValue dispatch *)

Map[f_, cons_Cons] ^:= LazyMap[f, cons]
Map[f_, cons_LazyList] ^:= LazyMap[f, cons]
Map[f_, LazyValue[x_]] ^:= LazyMap[f, x]

MapIndexed[f_, cons_Cons] ^:= LazyMapIndexed[f, cons]
MapIndexed[f_, cons_LazyList] ^:= LazyMapIndexed[f, cons]
MapIndexed[f_, LazyValue[x_]] ^:= LazyMapIndexed[f, x]

Select[cons_Cons, f_] ^:= LazySelect[cons, f]
Select[cons_LazyList, f_] ^:= LazySelect[cons, f]
Select[LazyValue[x_], f_] ^:= LazySelect[x, f]

(* Length[cons_Cons] ^:= LazyLength[cons]
Length[cons_LazyList] ^:= LazyLength[cons] *)

Drop[cons_Cons, n_] ^:= LazyDrop[cons, n]
Drop[cons_LazyList, n_] ^:= LazyDrop[cons, n]
Drop[LazyValue[x_], n_] ^:= LazyDrop[x, n]

Take[cons_Cons, n_] ^:= LazyTake[cons, n]
Take[cons_LazyList, n_] ^:= LazyTake[cons, n]
Take[LazyValue[x_], n_] ^:= LazyTake[x, n]

TakeWhile[cons_Cons, f_] ^:= LazyTakeWhile[cons, f]
TakeWhile[cons_LazyList, f_] ^:= LazyTakeWhile[cons, f]
TakeWhile[LazyValue[x_], f_] ^:= LazyTakeWhile[x, f]

DropWhile[cons_Cons, f_] ^:= LazyDropWhile[cons, f]
DropWhile[cons_LazyList, f_] ^:= LazyDropWhile[cons, f]
DropWhile[LazyValue[x_], f_] ^:= LazyDropWhile[x, f]

Append[cons_Cons, x_] ^:= LazyAppend[cons, x]
Append[cons_LazyList, x_] ^:= LazyAppend[cons, x]
Append[LazyValue[x_], y_] ^:= LazyAppend[x, y]

Prepend[cons_Cons, x_] ^:= LazyPrepend[cons, x]
Prepend[cons_LazyList, x_] ^:= LazyPrepend[cons, x]
Prepend[LazyValue[x_], y_] ^:= LazyPrepend[x, y]

First[cons_Cons, def___] ^:= LazyFirst[cons, def]
First[cons_LazyList, def___] ^:= LazyFirst[cons, def]
First[LazyValue[x_], def___] ^:= LazyFirst[x, def]

Rest[cons_Cons] ^:= LazyRest[cons]
Rest[cons_LazyList] ^:= LazyRest[cons]
Rest[LazyValue[x_]] ^:= LazyRest[x]

Catenate[cons_Cons] ^:= LazyCatenate[cons]
Catenate[cons_LazyList] ^:= LazyCatenate[cons]
Catenate[LazyValue[x_]] ^:= LazyCatenate[x]

Fold[fx__, cons_Cons] ^:= LazyFold[fx, cons]
Fold[fx__, cons_LazyList] ^:= LazyFold[fx, cons]
Fold[fx__, LazyValue[x_]] ^:= LazyFold[fx, x]

FoldList[fx__, cons_Cons] ^:= LazyFoldList[fx, cons]
FoldList[fx__, cons_LazyList] ^:= LazyFoldList[fx, cons]
FoldList[fx__, LazyValue[x_]] ^:= LazyFoldList[fx, x]

Join[cons__Cons] ^:= LazyJoin[cons]
Join[cons__LazyList] ^:= LazyJoin[cons]
Join[left___, LazyValue[x_], right___] ^:= LazyJoin[left, x, right]

Part[cons_Cons, n___] ^:= LazyPart[cons, n]
Part[cons_LazyList, n___] ^:= LazyPart[cons, n]
Part[LazyValue[x_], n___] ^:= LazyPart[x, n]

AllTrue[cons_Cons, f_] ^:= LazyAllTrue[cons, f]
AllTrue[cons_LazyList, f_] ^:= LazyAllTrue[cons, f]
AllTrue[LazyValue[x_], f_] ^:= LazyAllTrue[x, f]

AnyTrue[cons_Cons, f_] ^:= LazyAnyTrue[cons, f]
AnyTrue[cons_LazyList, f_] ^:= LazyAnyTrue[cons, f]
AnyTrue[LazyValue[x_], f_] ^:= LazyAnyTrue[x, f]

MapThread[f_, cons_Cons] ^:= LazyMapThread[f, cons]
MapThread[f_, cons_LazyList] ^:= LazyMapThread[f, cons]
MapThread[f_, LazyValue[x_]] ^:= LazyMapThread[f, x]
