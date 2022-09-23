Package["Wolfram`Lazy`"]

PackageExport["Cons"]
PackageExport["LazyList"]

PackageScope["LazyListQ"]

PackageExport["LazyListSublist"]
PackageScope["ConsLast"]
PackageExport["LazyListForm"]
PackageExport["LazyListToList"]

PackageExport["LazyLength"]
PackageExport["LazyAllTrue"]
PackageExport["LazyAnyTrue"]
PackageExport["LazyMemberQ"]

PackageExport["LazyListEmptyQ"]
PackageExport["LazyMap"]
PackageExport["LazyScan"]
PackageExport["LazyMapIndexed"]
PackageExport["LazySelect"]
PackageExport["LazyJoin"]
PackageExport["LazyAppend"]
PackageExport["LazyPrepend"]
PackageExport["LazyReverse"]
PackageExport["LazyCatenate"]
PackageExport["LazyFirst"]
PackageExport["LazyRest"]
PackageExport["LazyLast"]
PackageExport["LazyMost"]
PackageExport["LazyTake"]
PackageExport["LazyDrop"]
PackageExport["LazyTakeDrop"]
PackageExport["LazyTakeWhile"]
PackageExport["LazyDropWhile"]
PackageExport["LazyRotateLeft"]
PackageExport["LazyRotateRight"]
PackageExport["LazyDeleteDuplicates"]
PackageExport["LazyDeleteDuplicatesBy"]

PackageExport["LazyFoldLeft"]
PackageExport["LazyFold"]
PackageExport["LazyFoldList"]
PackageExport["LazyFoldRight"]
PackageExport["LazyFoldRightList"]
PackageExport["LazyMapThread"]
PackageExport["LazyTranspose"]

PackageExport["ToLazyList"]
PackageExport["LazyNest"]
PackageExport["LazyNestWhile"]
PackageExport["LazyNestList"]
PackageExport["LazyNestWhileList"]
PackageExport["LazyRange"]
PackageExport["LazyTable"]
PackageExport["LazyPartition"]
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
PackageExport["LazyRandomInteger"]


PackageExport["Lazy"]
Lazy::undef = "function `1` is undefined for the argument `2`."

SetAttributes[Cons, {HoldAll, Flat}]
SetAttributes[LazyList, {HoldAll}]

l_LazyList /; $LazyNoEntry && System`Private`EntryQ[Unevaluated[l]] := System`Private`SetNoEntry[Unevaluated[l]]
l_Cons /; $LazyNoEntry && System`Private`EntryQ[Unevaluated[l]] := System`Private`SetNoEntry[Unevaluated[l]]


LazyListQ[l_] := MatchQ[Unevaluated[l], _Cons | _LazyList]

LazyList[x_] := ToLazyList[x]
LazyList[Nothing, l_] := l


(* Functions *)

LazyListEmptyQ[h_[]] := True
LazyListEmptyQ[h_[l___]] /; FlatHoldQ[h] := ArgEval[h[l]] === h[]
LazyListEmptyQ[LazyValue[x_]] := LazyListEmptyQ[x]
LazyListEmptyQ[_] := False


LazyMap[f_, h_[]] /; HoldQ[h] := h[]
LazyMap[f_, h_[x_, l___]] /; FlatHoldQ[h] := h[f[x], LazyMap[f, ArgEval[h[l]]]]
LazyMap[f_, h_[x_, l_]] /; HoldQ[h] := h[f[x], LazyMap[f, l]]
LazyMap[f_, h_[l_]] /; HoldFirstQ[h] := h[LazyMap[f, l]]
LazyMap[f_, l_] := With[{r = l}, LazyValue[LazyMap[f, r]] /; LazyValueQ[r] || r =!= Unevaluated[l] || Message[Lazy::undef, LazyMap, r]]
LazyMap[f_][l_] := LazyMap[f, l]


LazyMapIndexed[f_, l_] := LazyMapThread[f, LazyList[l, LazyList[LazyMap[List, LazyRange[]], LazyList[]]]]


LazyScan[f_, h_[]] := Null
LazyScan[f_, h_[x_, l___]] /; FlatHoldQ[h] := (f[x]; LazyScan[f, ArgEval[h[l]]])
LazyScan[f_, h_[x_, l_]] /; HoldQ[h] := (f[x]; LazyScan[f, l])
LazyScan[f_, h_[l_]] /; HoldFirstQ[h] := LazyScan[f, l]
LazyScan[f_][l_] := LazyScan[f, l]


LazySelect[h_[], _] /; HoldQ[h] := h[]
LazySelect[h_[x_, l___], crit_] /; FlatHoldQ[h] :=
    With[{z = x}, If[TrueQ[crit[ReleaseLazyValue[z]]], h[z, LazySelect[ArgEval[h[l]], crit]], LazyValue @ LazySelect[ArgEval[h[l]], crit]]]
LazySelect[h_[x_, l_], crit_] /; HoldQ[h] := With[{z = x}, If[TrueQ[crit[ReleaseLazyValue[z]]], h[z, LazySelect[l, crit]], LazyValue @ LazySelect[l, crit]]]
LazySelect[h_[l_], crit_] /; HoldFirstQ[h] := h @ LazySelect[l, crit]
LazySelect[crit_][l_] := LazySelect[l, crit]


LazyFirst[h_[x_, l___], def___] /; FlatHoldQ[h] := With[{y = x}, If[LazyValueQ[y] || y === Unevaluated[x], y, LazyValue[LazyFirst[h[y, l]]]]]
LazyFirst[h_[x_, _], ___] /; HoldQ[h] := x
LazyFirst[h_[l_], def___] /; HoldFirstQ[h] := h[LazyFirst[l, def]]
LazyFirst[h_[], def_] /; HoldQ[h] := def
LazyFirst[h_[]] /; HoldQ[h] && Message[Lazy::undef, LazyFirst, h[]] := Null
LazyFirst[l : Except[h_[] /; HoldQ[h]], def___] := With[{r = l},
    LazyValue[LazyFirst[r, def]] /; LazyValueQ[r] || r =!= Unevaluated[l] || Message[Lazy::undef, LazyFirst, r]
]


LazyRest[h_[l___], ___] /; FlatHoldQ[h] := LazyValue @ Replace[ArgEval[h[l]], _[_, r___] :> h[r]]
LazyRest[h_[_, l_], ___] /; HoldQ[h] := l
LazyRest[h_[l_], def___] /; HoldFirstQ[h] := h[LazyRest[l, def]]
LazyRest[h_[], def_] /; HoldQ[h] := def
LazyRest[h_[]] /; HoldQ[h] && Message[Lazy::undef, LazyRest, l] := Null
LazyRest[l : Except[h_[] /; HoldQ[h]], def___] := With[{r = l},
    LazyValue[LazyRest[r, def]] /; LazyValueQ[r] || r =!= Unevaluated[l] || Message[Lazy::undef, LazyRest, r]
]


LazyLast[h_[x_], ___] /; FlatHoldQ[h] := x
LazyLast[h_[_, l__], def___] /; FlatHoldQ[h] := LazyValue[LazyLast[ArgEval[h[l]], def]]
LazyLast[h_[x_, l_], def___] /; HoldQ[h] := With[{r = l}, If[! LazyValueQ[r] && r === LazyList[], x, LazyValue[LazyLast[r, def]]]]
LazyLast[h_[l_], def___] /; HoldQ[h] := h[LazyLast[l, def]]
LazyLast[h_[]] /; HoldQ[h] && Message[Lazy::undef, LazyLast, h[]] := Null
LazyLast[h_[], def_] /; HoldQ[h] := def
LazyLast[l : Except[h_[] /; HoldQ[h]], def___] := With[{r = l},
    LazyValue[LazyLast[r, def]] /; LazyValueQ[r] || r =!= Unevaluated[l] || Message[Lazy::undef, LazyLast, r]
]


LazyMost[l : _[]] /; Message[Most::nomost, l] := Null
LazyMost[_[], def_] := def
LazyMost[h_[_], ___] /; FlatHoldQ[h] := h[]
LazyMost[h_[_, h_[]], ___] := h[]
LazyMost[_[l_], def___] := LazyValue[LazyMost[l, def]]
LazyMost[h_[x_, l___], ___] /; FlatHoldQ[h] := h[x, LazyMost[ArgEval[h[l]]]]
LazyMost[h_[x_, l_], ___] := h[x, LazyMost[l]]


LazyDrop[h_[], _] /; HoldQ[h] := h[]
LazyDrop[h_[_, l___], n_] /; FlatHoldQ[h] := If[n <= 0, h[], LazyValue[LazyDrop[ArgEval[h[l]], n - 1]]]
LazyDrop[l_, n_] /; n <= 0 := l
LazyDrop[h_[x_, l_], n_] /; HoldQ[h] := LazyValue[LazyDrop[l, n - 1]]
LazyDrop[h_[l_], n_] /; HoldFirstQ[h] := h[LazyDrop[l, n]]
LazyDrop[l_, n_] := With[{r = l}, LazyValue[LazyDrop[r, n]] /; r =!= Unevaluated[l] || Message[Lazy::undef, LazyDrop, r]]
LazyDrop[n_][l_] := LazyDrop[l, n]


LazyTake[h_[], _] /; HoldQ[h] := h[]
LazyTake[h_[x_, ___], 1] /; FlatHoldQ[h] := h[x, h[]]
LazyTake[h_[x_, l___], n_] /; FlatHoldQ[h] := h[x, LazyTake[ArgEval[h[l]], n - 1]]
LazyTake[h_[__], n_] /; HoldQ[h] && n <= 0 := h[]
LazyTake[h_[x_, _], 1] /; HoldQ[h] := h[x, h[]]
LazyTake[h_[x_, l_], n_] /; HoldQ[h] := h[x, LazyTake[l, n - 1]]
LazyTake[h_[l_], n_] /; HoldFirstQ[h] := h[LazyTake[l, n]]
LazyTake[l_, n_] := With[{r = l}, LazyValue[LazyTake[r, n]] /; r =!= Unevaluated[l] || Message[Lazy::undef, LazyTake, r]]
LazyTake[n_][l_] := LazyTake[Unevaluated[l], n]


LazyTakeDrop[h_[], _] := {h[], h[]}
LazyTakeDrop[h_[x_, l___], n_] /; FlatHoldQ[h] := If[n <= 0, {h[], h[x, l]}, Replace[LazyTakeDrop[ArgEval[h[l]], n - 1], {t_, d_} :> {h[x, t], d}]]
LazyTakeDrop[h_[x_, l_], n_] := {LazyTake[h[x, l], n], LazyDrop[h[x, l], n]}
LazyTakeDrop[h_[l_], n_] := LazyValue[LazyTakeDrop[l, n]]
LazyTakeDrop[n_][l_] := LazyTakeDrop[l, n]


LazyDropWhile[h_[], _] /; HoldQ[h] := h[]
LazyDropWhile[h_[x_, l___], crit_] /; FlatHoldQ[h] := If[TrueQ[crit[ReleaseLazyValue[x]]], LazyValue[LazyDropWhile[ArgEval[h[l]], crit]], h[x, l]]
LazyDropWhile[h_[x_, l_], crit_] /; HoldQ[h] := If[TrueQ[crit[ReleaseLazyValue[x]]], LazyValue[LazyDropWhile[l, crit]], h[x, l]]
LazyDropWhile[h_[l_], crit_] /; HoldFirstQ[h] := h[LazyDropWhile[l, crit]]
LazyDropWhile[crit_][l_] := LazyDropWhile[l, crit]


LazyTakeWhile[h_[], _] := h[]
LazyTakeWhile[h_[LazyValue[x_] | x_, l___], crit_] /; FlatHoldQ[h] := If[TrueQ[crit[ReleaseLazyValue[x]]], h[x, LazyTakeWhile[ArgEval[h[l]], crit]], h[]]
LazyTakeWhile[h_[LazyValue[x_] | x_, l_], crit_] := If[TrueQ[crit[ReleaseLazyValue[x]]], h[x, LazyTakeWhile[l, crit]], h[]]
LazyTakeWhile[h_[l_], crit_] := LazyValue[LazyTakeWhile[l, crit]]
LazyTakeWhile[crit_][l_] := LazyTakeWhile[l, crit]


LazyAppend[h_[], x_] := h[x, h[]]
LazyAppend[h_[x_, l___], y_] /; FlatHoldQ[h]:= h[x, LazyAppend[ArgEval[h[l]], y]]
LazyAppend[h_[x_, l_], y_] := h[x, LazyAppend[l, y]]
LazyAppend[h_[l_], x_] := LazyValue @ LazyAppend[l, x]
LazyAppend[x_][l_] := LazyAppend[l, x]


LazyPrepend[h_[], x_] /; HoldQ[h] := h[x, h[]]
LazyPrepend[h_[x_, l___], y_] /; FlatHoldQ[h] := h[y, x, l]
LazyPrepend[h_[x_, l_], y_] /; HoldQ[h] := h[y, h[x, l]]
(* LazyPrepend[h_[l_], x_] /; HoldFirstQ[h] := LazyPrepend[l, x] *)
LazyPrepend[l_, x_] := LazyList[x, ToLazyList[l]]
LazyPrepend[x_][l_] := LazyPrepend[l, x]


LazyReverse[h_[]] /; HoldQ[h] := h[]
LazyReverse[h_[x_, l___]] /; FlatHoldQ[h] := LazyValue @ LazyAppend[LazyReverse[ArgEval[h[l]]], x]
LazyReverse[h_[x_, l_]] /; HoldQ[h] := LazyValue @ LazyAppend[LazyReverse[l], x]
LazyReverse[h_[l_]] /; HoldFirstQ[h] := h @ LazyReverse[l]


LazyJoin[h_[]] /; HoldQ[h] := h[]
LazyJoin[h_[], rest__] /; HoldQ[h] := LazyValue @ LazyJoin[rest]
LazyJoin[h_[l_], rest___] /; FlatHoldQ[h] := h[l, rest]
LazyJoin[h_[x__, l_], rest___] /; FlatHoldQ[h] := h[x, LazyJoin[h[l], rest]]
LazyJoin[h_[x_, l_], rest___] /; HoldQ[h] := h[x, LazyJoin[l, rest]]
LazyJoin[h_[l_], rest___] /; HoldFirstQ[h] := h[LazyJoin[l, rest]]
LazyJoin[l_, rest___] := With[{r = l}, LazyJoin[r, rest] /; LazyValueQ[r] || r =!= Unevaluated[l] || Message[Lazy::undef, LazyJoin, r]]
SetAttributes[LazyJoin, HoldRest]

LazyCatenate[h_[]] /; HoldQ[h] := h[]
LazyCatenate[h_[g_[]]] /; HoldQ[h] && HoldQ[g] := h[]
LazyCatenate[h_[g_[], l_]] /; HoldQ[h] && HoldQ[g] := LazyValue @ LazyCatenate[l]
LazyCatenate[h_[g_[x_, l_], rest___]] /; FlatHoldQ[h] && HoldQ[g] := h[x, LazyJoin[LazyCatenate[h[l]], LazyCatenate[ArgEval[h[ArgEval[rest]]]]]]
LazyCatenate[h_[x_, rest___]] /; FlatHoldQ[h] := With[{y = x}, LazyValue @ LazyCatenate[h[y, rest]] /; LazyValueQ[y] || y =!= Unevaluated[x] || Message[Lazy::undef, LazyCatenate, h[y, rest]]]
LazyCatenate[h_[l___], rest___] /; FlatHoldQ[h] := h[l, rest]
LazyCatenate[h_[x_, l_]] /; HoldQ[h] := LazyValue @ LazyJoin[x, LazyCatenate[l]]
LazyCatenate[h_[l_]] /; HoldFirstQ[h] := h @ LazyCatenate[l]
LazyCatenate[l_] := With[{r = ArgEval[l]}, LazyCatenate[r] /; LazyValueQ[r] || r =!= Unevaluated[l] || Message[Lazy::undef, LazyCatenate, r]]


LazyFoldLeft[_, x_, h_[]] /; HoldQ[h] := x
LazyFoldLeft[f_, h_[x_, l___]] /; FlatHoldQ[h] := LazyFoldLeft[f, x, ArgEval[h[l]]]
LazyFoldLeft[f_, x_, h_[y_, l___]] /; FlatHoldQ[h] := LazyValue @ LazyFoldLeft[f, Unevaluated[f[x, y]], ArgEval[h[l]]]
LazyFoldLeft[f_, h_[x_, l_]] /; HoldQ[h] := LazyFoldLeft[f, x, l]
LazyFoldLeft[f_, x_, h_[y_, l_]] /; HoldQ[h] := LazyValue @ LazyFoldLeft[f, Unevaluated[f[x, y]], l]
LazyFoldLeft[f_, h_[l_]] /; HoldFirstQ[h] := h[LazyFoldLeft[f, l]]
LazyFoldLeft[f_, x_, h_[l_]] /; HoldFirstQ[h] := h[LazyFoldLeft[f, x, l]]
LazyFoldLeft[f_][l_] := LazyFoldLeft[f, l]


LazyFold[_, x_, h_[]] /; HoldQ[h] := x
LazyFold[f_, h_[x_, l___]] /; FlatHoldQ[h] := LazyFold[f, x, ArgEval[h[l]]]
LazyFold[f_, x_, h_[y_, l___]] /; FlatHoldQ[h] := LazyValue @ LazyFold[f, f[x, y], ArgEval[h[l]]]
LazyFold[f_, h_[x_, l_]] := LazyFold[f, x, l]
LazyFold[f_, x_, h_[y_, l_]] := LazyValue @ LazyFold[f, f[x, y], l]
LazyFold[f_, h_[l_]] /; HoldFirstQ[h] := h[LazyFold[f, l]]
LazyFold[f_, x_, h_[l_]] /; HoldFirstQ[h] := h[LazyFold[f, x, l]]
LazyFold[f_][l_] := LazyFold[f, l]


LazyFoldRight[f_, x_, h_[]] := x
LazyFoldRight[f_, h_[x_, l___]] /; FlatHoldQ[h] := f[LazyFoldRight[f, ArgEval[h[l]]], x]
LazyFoldRight[f_, x_, h_[y_, l___]] /; FlatHoldQ[h] := f[y, LazyFoldRight[f, x, ArgEval[h[l]]]]
LazyFoldRight[f_, h_[x_, l_]] := f[x, LazyFoldRight[f, l]]
LazyFoldRight[f_, x_, h_[y_, l_]] := f[y, LazyFoldRight[f, x, l]]
LazyFoldRight[f_, h_[l_]] := LazyValue[LazyFoldRight[f, l]]
LazyFoldRight[f_, x_, h_[l_]] := LazyValue[LazyFoldRight[f, x, l]]
LazyFoldRight[f_][l_] := LazyFoldRight[f, l]


LazyFoldList[_, x_, h_[]] := h[x, h[]]
LazyFoldList[f_, h_[x_, l___]] /; FlatHoldQ[h] := LazyFoldList[f, x, ArgEval[h[l]]]
LazyFoldList[f_, x_, h_[y_, l___]] /; FlatHoldQ[h] := With[{z = f[x, y]}, h[x, LazyFoldList[f, z, ArgEval[h[l]]]]]
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
        With[{xs = Quiet[Check[Map[ReleaseLazyValue @ LazyFirst[#] &, l], {}, Lazy::undef], Lazy::undef]},
            If[ Length[xs] < Length[l],
                LazyList[],
                LazyList[f @@ xs, LazyMapThread[f, Map[LazyRest, l]]]
            ]
        ]
    ]

LazyMapThread[_, h_Symbol[]] := h[]
LazyMapThread[_, _[], head_Symbol] := head[]
LazyMapThread[f_, l : h_Symbol[__]] := LazyMapThread[f, l, h]
LazyMapThread[f_, l : _[__], head_Symbol] := With[{r = LazyTakeWhile[l, MatchQ[_head]]},
    If[ r === head[],
        head[],
        With[{xs = Quiet[Check[LazyListToList[LazyMap[LazyFirst, r]], {}, Lazy::undef], Lazy::undef]},
            If[ Length[xs] > 0,
                head[f @@ xs, LazyMapThread[f, LazyMap[LazyRest, r], head]],
                head[]
            ]
        ]
    ]
]


LazyTranspose[l_] := With[{r = ArgEval @ LazyMap[ReleaseLazyValue, l]},
    LazyTakeWhile[# =!= LazyList[] &] @ LazyList[
        LazySelect[LazyMap[LazyFirst[#, Nothing] &, r], # =!= Nothing &],
        LazyTranspose[LazySelect[LazyMap[LazyRest[#, Nothing] &, r], # =!= Nothing &]]
    ]
]

LazyRotateLeft[h_[]] := h[]
LazyRotateLeft[h_[LazyValue[x_] | x_, l___]] /; FlatHoldQ[h] := LazyAppend[ArgEval[h[l]], x]
LazyRotateLeft[h_[LazyValue[x_] | x_, l_]] := LazyAppend[l, x]
LazyRotateLeft[h_[x_]] := LazyValue[LazyRotateLeft[x]]
LazyRotateLeft[l_, n_ : 0] := LazyNest[LazyRotateLeft, l, n]


LazyRotateRight[h_[]] := h[]
LazyRotateRight[h_[LazyValue[x_] | x_, l___]] /; FlatHoldQ[h] := With[{r = LazyValue @ LazyRotateRight[ArgEval[h[l]]]}, h[LazyFirst[r], h[x, LazyRest[r]]]]
LazyRotateRight[h_[LazyValue[x_] | x_, l_]] := With[{r = LazyValue @ LazyRotateRight[l]}, If[LazyListEmptyQ[l], h[x], h[LazyFirst[r], h[x, LazyRest[r]]]]]
LazyRotateRight[h_[x_]] := LazyValue[LazyRotateRight[x]]
LazyRotateRight[l_, n_ : 0] := LazyNest[LazyRotateRight, l, n]


lazyDeleteDuplicates[h_[], _] /; HoldQ[h] := h[]
lazyDeleteDuplicates[h_[x_, l_], pre_List] /; HoldQ[h] := With[{z = ReleaseLazyValue[x]}, If[MemberQ[pre, z], lazyDeleteDuplicates[l, pre], h[x, lazyDeleteDuplicates[l, Append[pre, z]]]]]
lazyDeleteDuplicates[h_[l_], pre_List] /; HoldFirstQ[h] := h[lazyDeleteDuplicates[l, pre]]

LazyDeleteDuplicates[l_] := lazyDeleteDuplicates[l, {}]


lazyDeleteDuplicatesBy[h_[], _, _] /; HoldQ[h] := h[]
lazyDeleteDuplicatesBy[h_[x_, l_], f_, pre_List] /; HoldQ[h] := With[{z = f[ReleaseLazyValue[x]]}, If[MemberQ[pre, z], lazyDeleteDuplicatesBy[l, f, pre], h[x, lazyDeleteDuplicatesBy[l, f, Append[pre, z]]]]]
lazyDeleteDuplicatesBy[h_[l_], f_, pre_List] /; HoldFirstQ[h] := h[lazyDeleteDuplicatesBy[l, f, pre]]

LazyDeleteDuplicatesBy[l_, f_] := lazyDeleteDuplicatesBy[l, f, {}]
LazyDeleteDuplicatesBy[f_][l_] := LazyDeleteDuplicatesBy[l, f]


(* Queries *)

LazyLength[h_[]] /; HoldQ[h] := Nat[]
LazyLength[h_[_, l___]] /; FlatHoldQ[h] := Nat[LazyLength[ArgEval[h[l]]], 1]
LazyLength[h_[_, l_]] /; HoldQ[h] := Nat[LazyLength[l], 1]
LazyLength[h_[l_]] /; HoldFirstQ[h] := h[LazyLength[l]]


LazyAllTrue[h_[], _] := True
LazyAllTrue[h_[LazyValue[x_] | x_, l___], test_] /; FlatHoldQ[h] := If[test[x], LazyAllTrue[ArgEval[h[l]], test], False]
LazyAllTrue[h_[LazyValue[x_] | x_, l_], test_] := If[test[x], LazyAllTrue[l, test], False]
LazyAllTrue[h_[l_], test_] := LazyValue[LazyAllTrue[l, test]]


LazyAnyTrue[h_[], _] := False
LazyAnyTrue[h_[LazyValue[x_] | x_, l___], test_] /; FlatHoldQ[h] := If[test[x], True, LazyAnyTrue[h[l], test]]
LazyAnyTrue[h_[LazyValue[x_] | x_, l_], test_] := If[test[x], True, LazyAnyTrue[l, test]]
LazyAnyTrue[h_[l_], test_] := LazyValue[LazyAnyTrue[l, test]]


LazyMemberQ[h_[], _] /; HoldQ[h] := False
LazyMemberQ[h_[x_, l_], y_] /; HoldQ[h]:= If[x === y, True, LazyValue @ LazyMemberQ[l, y]]
LazyMemberQ[h_[l_], y_] /; HoldFirstQ[h] := h[LazyMemberQ[l, y]]


(* Generators *)

ToLazyList[l : h_[___], h_ : LazyList] := l
ToLazyList[{x_, rest___}, h_ : LazyList] := h[x, ToLazyList[{rest}, h]]
ToLazyList[{}, h_ : LazyList] := h[]
ToLazyList[g_[x_, rest___], h_ : LazyList] /; FlatHoldQ[g] := h[x, ToLazyList[ArgEval[g[rest]], h]]
ToLazyList[g_[x_, rest_], h_ : LazyList] /; HoldQ[g] := h[x, ToLazyList[rest, h]]
ToLazyList[g_[], h_ : LazyList] /; HoldQ[g] := h[]
ToLazyList[g_[x_], h_ : LazyList] /; HoldFirstQ[g] := g[ToLazyList[x, h]]
ToLazyList[x_, h_ : LazyList] := h[x, h[]]


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


LazyRange[from : _ ? NumericQ, to : _ ? NumericQ | Infinity, step : _ ? NumericQ : 1, h_Symbol] :=
    If[from > to && step > 0 || from < to && step < 0, h[],
        With[{next = from + step}, h[from, LazyRange[next, to, step, h]]]
    ]
LazyRange[from : _ ? NumericQ, to : _ ? NumericQ | Infinity | _Nat, step : _ ? NumericQ : 1] := LazyRange[from, to, step, LazyList]
LazyRange[to  : _ ? NumericQ | Infinity | _Nat, h_Symbol : LazyList] := LazyRange[1, to, h]
LazyRange[h_Symbol : LazyList] := LazyRange[Nat[Infinity], h]

LazyRange[from : _ ? NumericQ, Nat[to_, n_Integer ? Positive], step : _ ? NumericQ : 1, h_Symbol] :=
    h[from, LazyRange[from + step, Nat[to, n - 1], step, h]]

LazyRange[from_, Nat[x_, 0], step_, h_Symbol] := LazyRange[from, x, step, h]


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


LazyPartition[h_[], _] := h[]
LazyPartition[l : h_[__], n_] := h[#1, LazyPartition[#2, n]] & @@ LazyTakeDrop[l, n]
LazyPartition[LazyValue[x_], n_] := LazyValue[LazyPartition[x, n]]


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


LazyPermutations[xs_] := With[{len = Length[xs]}, If[len > 0, LazyMap[xs[[ ResourceFunction["PermutationFromIndex"][#, len] ]] &, LazyRange[len !]], LazyList[xs, LazyList[]]]]


Options[lazyPosition] = Options[Position]
lazyPosition[expr : head_[args___], patt_, pos_List, opts : OptionsPattern[]] := LazyJoin[
    If[TrueQ[OptionValue[Heads]], lazyPosition[Unevaluated[head], patt, Append[pos, 0], opts], LazyList[]],
    If[
        MatchQ[Unevaluated[expr], patt],
        LazyList[pos, LazyCatenate @ LazyMapIndexed[Function[{arg, p}, lazyPosition[Unevaluated[arg], patt, Join[pos, p], opts], HoldFirst], ToLazyList @ Unevaluated[{args}]]],
        LazyCatenate @ LazyMapIndexed[Function[{arg, p}, lazyPosition[Unevaluated[arg], patt, Join[pos, p]], HoldFirst], ToLazyList @ Unevaluated[{args}]]
    ]
]
lazyPosition[expr_, patt_, pos_List, OptionsPattern[]] := If[MatchQ[Unevaluated[expr], patt], LazyList[pos, LazyList[]], LazyList[]]

Options[LazyPosition] = Options[Position]
LazyPosition[expr_, patt_, opts : OptionsPattern[]] := lazyPosition[Unevaluated[expr], patt, {}, opts]
LazyPosition[expr_] := LazyPosition[Unevaluated[expr], _]


LazySubdivide[min_, max_, n : _Integer ? NonNegative] := min + (max - min)/n LazyRange[0, n]
LazySubdivide[n : _Integer ? NonNegative] := LazySubdivide[0, 1, n]
LazySubdivide[max_, n : _Integer ? NonNegative] := LazySubdivide[0, max, n]

LazyRests[l_] := LazyNestList[LazyRest, l]


LazyArray[f_, LazyList[], LazyList[]] := f[]
LazyArray[f_, ns_LazyList, rs_LazyList] :=
	Map[x |-> LazyArray[f[x, ##] &, Rest[ns], Rest[rs]], If[ListQ[#2], LazySubdivide[Sequence @@ Take[#2, UpTo[2]], #1 - 1], #2 - 1 + LazyRange[#1]] &[First[ns], First[rs]]]
LazyArray[f_, ns : {(_Integer ? NonNegative | Infinity | _Nat)...}, rs_List] /; Length[ns] == Length[rs] || Message[Array::plen, ns, rs] :=
	LazyArray[f, LazyList[ns], LazyList[rs]]
LazyArray[f_, ns : {(_Integer ? NonNegative | Infinity | _Nat)...}] := LazyArray[f, ns, ConstantArray[1, Length[ns]]]
LazyArray[f_, ns_LazyList] := LazyArray[f, ns, LazyConstantArray[1, LazyLength[ns]]]
LazyArray[f_, n : _Integer ? NonNegative | Infinity | _Nat : Infinity, r_ : 1] := LazyArray[f, {n}, {r}]


LazyConstantArray[c_, LazyList[]] := c
LazyConstantArray[c_, ns_LazyList] := LazyMap[x |-> LazyConstantArray[c, LazyRest[ns]], LazyRange[LazyFirst[ns]]]
LazyConstantArray[c_, ns_] := LazyConstantArray[c, LazyList[ns]]
LazyConstantArray[c_] := LazyConstantArray[c, {Infinity}]


LazyRandomInteger[max_Integer] := LazyRandomInteger[{0, max}]
LazyRandomInteger[] := LazyRandomInteger[{0, 1}]
LazyRandomInteger[range_, ns_ : {Infinity}] := LazyArray[RandomInteger[range] &, ns]


(* Listable *)

Cons /: f_Symbol[cons___Cons] /; MemberQ[Attributes[f], Listable] := LazyMapThread[f, {cons}]
LazyList /: f_Symbol[cons___LazyList] /; MemberQ[Attributes[f], Listable] := LazyMapThread[f, {cons}]

Cons /: f_Symbol[left___, cons_Cons, right___] /; MemberQ[Attributes[f], Listable] := LazyMap[f[left, #, right] &, cons]
LazyList /: f_Symbol[left___, cons_LazyList, right___] /; MemberQ[Attributes[f], Listable] := LazyMap[f[left, #, right] &, cons]


(* Formatting *)

(* LazyListToList[LazyValue[x_]] := LazyListToList[x] *)
LazyListToList[cons : _LazyList | _Cons | ((head : Except[LazyTree | Hold | HoldComplete, _Symbol])[___] /; HoldQ[head])] := With[{
    hh = Head[cons]
},
Block[{x = Hold[cons], l = {}},
    CheckAbort[
        While[
            MatchQ[x, Hold[_hh | _LazyValue | _LazyExpression]],
            Replace[x, {
                Hold[hh[]] :> Break[],
                Hold[hh[y__, z_]] /; FlatHoldQ[hh] :> (
                    l = Join[l, {y}];
                    x = Hold[Evaluate[hh[Evaluate[z]]]]
                ),
                Hold[hh[y_]] /; FlatHoldQ[hh] :> (
                    With[{v = ReleaseLazyValue[Evaluate[y]]}, If[MatchQ[Unevaluated[v], _Sequence], l = Join[l, {v}], AppendTo[l, v]]];
                    Break[]
                ),
                Hold[hh[y_, z_]] :> With[{v = ReleaseLazyValue[Evaluate[y]]}, If[MatchQ[Unevaluated[v], _Sequence], l = Join[l, {v}], AppendTo[l, v]]; x = Hold[Evaluate[z]]],
                Hold[l_LazyExpression] :> (x = Hold[Evaluate[l["Eval"]]]),
                Hold[z_] :> (x = Hold[Evaluate[ReleaseLazyValue[z]]])
             }]
        ],
        Null
    ];
    If[ !MatchQ[cons, _LazyValue | _LazyList | _Cons],
        l = hh @@ l
    ];
    l
]
]
LazyListToList[x_] := x


(* LazyListSublist[h_[x___, l : h_[___]]] /; FlatHoldQ[h] := {x, Splice[LazyListSublist[Unevaluated[l]]]} *)
LazyListSublist[Cons[x_]] := {x}
LazyListSublist[Cons[x___, l_]] := {x}
LazyListSublist[LazyList[x_, l : LazyList[___]]] := {x, Splice[LazyListSublist[Unevaluated[l]]]}
LazyListSublist[LazyList[x_, l_]] := {x}
LazyListSublist[(Cons | LazyList)[]] := {}
LazyListSublist[_] := {}


ConsLast[Cons[___, l_]] := h[l]
ConsLast[LazyList[___, l_]] := ConsLast[Unevaluated[l]]
ConsLast[(h : Cons | LazyList)[]] := h[]
ConsLast[x_] := x


LazyListForm[cons : _Symbol[LazyValue[x_] | x_, _[]]] := Tooltip[{x}, InputForm[cons]]

LazyListForm[cons : _Symbol[]] := Tooltip[{}, InputForm[cons]]
LazyListForm[cons : head_Symbol[Longest[x__], l_]] := DynamicModule[{values = {x}, placeholder = Null, new, rest},
    rest = If[FlatHoldQ[head],
        Hold[Evaluate[ArgEval[head[l]]]],
        Hold @ Evaluate @ ReleaseHold @ FixedPoint[Replace[{
            Hold[LazyList[y_, next_]] :> (
                If[MatchQ[Unevaluated[y], _Sequence], values = Join[values, {y}], AppendTo[values, y]];
                Hold[next]
            )
            }],
            Hold[l]
        ]
    ];
    new = Hold[placeholder];
    Tooltip[
        Row[{"{", Row[{
            Row[values, ","],
            Dynamic @ If[placeholder === Null, Row[{}], placeholder],
            Dynamic @ If[ValueQ[rest], Row[{", ", Tooltip[
                Button[
                    Framed["\[Ellipsis]"],
                    DynamicModule[{newElement, newPlaceholder = Null, release},
                        release = Replace[{
                            Hold[h_[y_, next___]] /; FlatHoldQ[h] :> (
                                If[ TrueQ[CurrentValue["OptionKey"]],
                                    With[{z = ReleaseLazyValue[y]},
                                        newElement = z;
                                        If[ LazyValueQ[y] || z =!= Unevaluated[y],
                                            rest = Hold[h[z, next]];
                                            release[rest],
                                            rest = Hold[Evaluate[ArgEval[h[next]]]]
                                        ]
                                    ],

                                    With[{z = y},
                                        newElement = z;
                                        If[ LazyValueQ[y] || z =!= Unevaluated[y],
                                            rest = Hold[h[z, next]],
                                            rest = Hold[Evaluate[ArgEval[h[next]]]]
                                        ]
                                    ]
                                ];
                            ),
                            Hold[h_[y_, next_]] /; HoldQ[h] :> (
                                If[ TrueQ[CurrentValue["OptionKey"]],
                                    With[{z = ReleaseLazyValue[y]},
                                        newElement = z;
                                        rest = Hold[Evaluate[next]]
                                    ],
                                    With[{z = LazyValueEval[y]},
                                        newElement = z;
                                        If[ LazyValueQ[z],
                                            rest = Hold[h[z, next]],
                                            rest = Hold[Evaluate[next]]
                                        ]
                                    ]
                                ];
                            ),
                            Hold[LazyValue[next_]] :> (If[TrueQ[CurrentValue["OptionKey"]], rest = Hold[Evaluate[ReleaseLazyValue[next]]]; release[rest], rest = Hold[Evaluate[next]]]),
                            Hold[h_[next_]] /; HoldQ[h]  :> (rest = Hold[Evaluate[next]]),
                            Hold[_[]] :> Clear[rest],
                            Hold[y_] :> (newElement = y; Clear[rest])
                        }];
                        release[rest];
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
                DisableFormatting /@ HoldForm @@ rest
            ]}], Row[{}]]}
            ],
            "}"
        }],
        InputForm[cons]
    ]
]
LazyListForm[cons : h_Symbol[LazyValue[x_] | x_]] /; HoldQ[h] && FlatHoldQ[h] := Tooltip[{x}, InputForm[cons]]
LazyListForm[h_Symbol[LazyValue[x_] | x_]] /; HoldQ[h] := Format[LazyValue[x]]


l_Cons["DynamicList"] := LazyListForm[l]
l_LazyList["DynamicList"] := LazyListForm[l]

LazyListBoxes[l_, form_] := With[{
    icon = ""
},
    BoxForm`ArrangeSummaryBox[
        "LazyList",
        l,
        icon,
        {{BoxForm`SummaryItem[{l["DynamicList"]}]}},
        {{BoxForm`SummaryItem[{"Attributes: ", Attributes[Evaluate[Head[l]]]}]}},
        form,
		"Interpretable" -> Automatic
	]
]

MakeBoxes[l_Cons, form_] ^:= LazyListBoxes[l, form]
MakeBoxes[l_LazyList, form_] ^:= LazyListBoxes[l, form]


LazyList[x : Except[_LazyValue], l_] /; TrueQ[$LazyCache] := LazyList[LazyValue[x], l]
LazyList[x_, l : Except[_LazyValue]] /; TrueQ[$LazyCache] := LazyList[x, LazyValue[l]]
LazyList[x : Except[_LazyValue], l : Except[_LazyValue]] /; TrueQ[$LazyCache] := LazyList[LazyValue[x], LazyValue[l]]


(* UpValue dispatch *)

Map[f_, cons_Cons] ^:= LazyMap[f, cons]
Map[f_, cons_LazyList] ^:= LazyMap[f, cons]
Map[f_, LazyValue[x_]] ^:= LazyMap[f, x]

MapIndexed[f_, cons_Cons] ^:= LazyMapIndexed[f, cons]
MapIndexed[f_, cons_LazyList] ^:= LazyMapIndexed[f, cons]
MapIndexed[f_, LazyValue[x_]] ^:= LazyMapIndexed[f, x]

Scan[f_, cons_Cons] ^:= LazyScan[f, cons]
Scan[f_, cons_LazyList] ^:= LazyScan[f, cons]
Scan[f_, LazyValue[x_]] ^:= LazyScan[f, x]

Select[cons_Cons, f_] ^:= LazySelect[cons, f]
Select[cons_LazyList, f_] ^:= LazySelect[cons, f]
Select[LazyValue[x_], f_] ^:= LazySelect[x, f]

Length[cons_Cons] ^:= LazyLength[cons]
Length[cons_LazyList] ^:= LazyLength[cons]
Length[LazyValue[x_]] ^:= LazyLength[x]

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

TakeDrop[cons_Cons, n_] ^:= LazyTakeDrop[cons, n]
TakeDrop[cons_LazyList, n_] ^:= LazyTakeDrop[cons, n]
TakeDrop[LazyValue[x_], n_] ^:= LazyTakeDrop[x, n]

Append[cons_Cons, x_] ^:= LazyAppend[cons, x]
Append[cons_LazyList, x_] ^:= LazyAppend[cons, x]
Append[LazyValue[x_], y_] ^:= LazyAppend[x, y]

Prepend[cons_Cons, x_] ^:= LazyPrepend[cons, x]
Prepend[cons_LazyList, x_] ^:= LazyPrepend[cons, x]
Prepend[LazyValue[x_], y_] ^:= LazyPrepend[x, y]

First[cons_Cons, def___] ^:= LazyFirst[cons, def]
First[cons_LazyList, def___] ^:= LazyFirst[cons, def]
First[LazyValue[x_], def___] ^:= LazyFirst[x, def]

Last[cons_Cons, def___] ^:= LazyLast[cons, def]
Last[cons_LazyList, def___] ^:= LazyLast[cons, def]
Last[LazyValue[x_], def___] ^:= LazyLast[x, def]

Rest[cons_Cons] ^:= LazyRest[cons]
Rest[cons_LazyList] ^:= LazyRest[cons]
Rest[LazyValue[x_]] ^:= LazyRest[x]

Most[cons_Cons] ^:= LazyMost[cons]
Most[cons_LazyList] ^:= LazyMost[cons]
Most[LazyValue[x_]] ^:= LazyMost[x]

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

Partition[cons_Cons, n_] ^:= LazyPartition[cons, n]
Partition[cons_LazyList, n_] ^:= LazyPartition[cons, n]
Partition[LazyValue[x_], n_] ^:= LazyPartition[x, n]

RotateLeft[cons_Cons, n_] ^:= LazyRotateLeft[cons, n]
RotateLeft[cons_LazyList, n_] ^:= LazyRotateLeft[cons, n]
RotateLeft[LazyValue[x_], n_] ^:= LazyRotateLeft[x, n]

RotateRight[cons_Cons, n_] ^:= LazyRotateRight[cons, n]
RotateRight[cons_LazyList, n_] ^:= LazyRotateRight[cons, n]
RotateRight[LazyValue[x_], n_] ^:= LazyRotateRight[x, n]

Transpose[cons_LazyList] ^:= LazyTranspose[cons]

