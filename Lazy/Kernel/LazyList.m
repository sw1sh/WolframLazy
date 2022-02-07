Package["Lazy`"]

PackageExport["Cons"]
PackageExport["LazyList"]
PackageExport["LazyListQ"]
PackageExport["LazyListForm"]
PackageExport["LazyEval"]

PackageExport["Clone"]
PackageExport["Repeat"]
PackageExport["LazyDrop"]
PackageExport["LazyJoin"]
PackageExport["LazyRange"]
PackageExport["LazyTable"]
PackageExport["LazyParallelMap"]
PackageExport["Zip"]
PackageExport["ZipWith"]
PackageExport["FoldRight"]



SetAttributes[Cons, HoldAll]

Cons[x_] := Cons[x, Cons[]]


Length[Cons[]] ^:= 0
Length[Cons[_, l_]] ^:= 1 + With[{r = l}, If[MatchQ[r, _Cons], Length[l], 1]]


Map[_, Cons[]] ^:= Cons[]
Map[f_, Cons[x_, l_]] ^:= With[{y = f[x]}, Cons[y, Map[f, l]]]


Scan[_, Cons[]] ^:= Null
Scan[f_, Cons[x_, l_]] ^:= (f[x]; Scan[f, l])


Select[Cons[], _] ^:= Cons[]
Select[Cons[x_, l_], crit_] ^:= If[crit[x], Cons[x, Select[l, crit]], Select[l, crit]]


AnyTrue[Cons[], _] ^:= False
AnyTrue[Cons[x_, l_], test_] ^:= If[test[x], True, AnyTrue[l, test]]


AllTrue[Cons[], _] ^:= True
AllTrue[Cons[x_, l_], test_] ^:= If[test[x], AllTrue[l, test], False]


First[Cons[x_, _]] ^:= x


Rest[Cons[_, l_]] ^:= l


Take[Cons[], _] ^:= Cons[]
Take[Cons[x_, l_], n_] ^:= If[n <= 0, Cons[], Cons[x, Take[l, n - 1]]]


LazyDrop[Cons[], _] := Cons[]
LazyDrop[l : Cons[_, r_], n_] ^:= If[n <= 0, l, LazyDrop[r, n - 1]]
SetAttributes[LazyDrop, HoldFirst]


Drop[Cons[], _] ^:= Cons[]
Drop[Cons[x_, l_], n_] ^:= If[n <= 0, Cons[x, l], Drop[l, n - 1]]


Cons /: Part[l_Cons, from_ ;; to_] := Take[Drop[l, from - 1], to - from + 1]
Cons /: Part[l_Cons, n_Integer ? Positive] := First[Drop[l, n - 1]]


TakeDrop[Cons[], _] ^:= {Cons[], Cons[]}
TakeDrop[Cons[x_, l_], n_] ^:= If[n <= 0, {Cons[], Cons[x, l]}, MapAt[Prepend[#, x] &, TakeDrop[l, n - 1], {1}]]


Partition[Cons[], _] ^:= Cons[]
Partition[l_Cons, n_] ^:= Cons[#1, Partition[#2, n]] & @@ TakeDrop[l, n]


LazyJoin[Cons[]] ^:= Cons[]
LazyJoin[Cons[], rest__] ^:= LazyJoin[rest]
LazyJoin[Cons[x_, l_], rest___] ^:= Cons[x, LazyJoin[l, rest]]


Clone[Cons[]] ^:= Cons[]
Clone[l_Cons] ^:= LazyJoin[l, Clone[l]]


Repeat[x_] := Cons[x, Repeat[x]]


Catenate[Cons[Cons[x_, l_], r_]] ^:= Cons[x, LazyJoin[l, Catenate @ r]]
Catenate[Cons[]] ^:= Cons[]


LazyParallelMap[f_, l_Cons] ^:= Catenate @ Map[Map[ParallelSubmit[f[#]] &, #] &, Partition[l, $KernelCount]]


TakeWhile[Cons[], _] ^:= Cons[]
TakeWhile[Cons[x_, l_], crit_] ^:= If[crit[x], Cons[x, TakeWhile[l, crit]], Cons[]]


DropWhile[Cons[], _] := Cons[]
DropWhile[Cons[x_, l_], crit_] := If[crit[x], DropWhile[l, crit], l]


Append[Cons[], x_] ^:= Cons[x]
Append[Cons[x_, l_], y_] ^:= Cons[x, Append[l, y]]


Prepend[Cons[], x_] ^:= Cons[x]
Prepend[l_Cons, y_] ^:= Cons[y, l]


Reverse[Cons[]] ^:= Cons[]
Reverse[Cons[x_, l_]] ^:= Append[Reverse[l], x]


Fold[f_, Cons[x_, l_]] ^:= Fold[f, x, l]
Fold[f_, x_, Cons[]] ^:= f[x]
Fold[f_, x_, Cons[y_, l_]] ^:= Fold[f, f[x, y], l]


FoldList[f_, Cons[x_, l_]] ^:= FoldList[f, x, l]
FoldList[f_, x_, Cons[]] ^:= Cons[x]
FoldList[f_, x_, Cons[y_, l_]] ^:= With[{z = f[x, y]}, Cons[x, FoldList[f, z, l]]]


FoldRight[f_, Cons[x_, l_]] := f[x, FoldRight[f, l]]
FoldRight[f_, x_, Cons[y_, l_]] := f[y, FoldRight[f, x, l]]
FoldRight[_, _, Cons[]] := Cons[]
FoldRight[_, Cons[]] := Cons[]


Zip[Cons[], Cons[]] := Cons[]
Zip[Cons[_, _], Cons[]] := Cons[]
Zip[Cons[], Cons[_, _]] := Cons[]
Zip[Cons[x_, l_], Cons[y_, r_]] := Cons[{x, y}, Zip[l, r]]


ZipWith[f_][l_Cons, r_Cons] := Map[Apply[f], Zip[l, r]]


LazyRange[from_, to_] := If[from > to, Cons[], With[{next = from + 1}, Cons[from, LazyRange[next, to]]]]
LazyRange[to_] := LazyRange[1, to]
LazyRange[] := LazyRange[Infinity]


LazyTable[expr_, {var_Symbol, from_, to_}] := If[
    from > to,
    Cons[],
    With[{
        next = from + 1
    },
        Cons[Block[{var = from}, expr], LazyTable[expr, {var, next, to}]]
    ]
]
LazyTable[expr_, {var_Symbol, to_}] := LazyTable[expr, {var, 1, to}]
LazyTable[expr_, var_Symbol] := LazyTable[expr, {var, Infinity}]
SetAttributes[LazyTable, HoldFirst]


ToList[cons_Cons] := Module[{
    x = cons, l = {}
},
    CheckAbort[
        While[
            MatchQ[x, _Cons],
            If[ x === Cons[],
                Break[],
                AppendTo[l, First[x]];
                x = Last[x]
             ]
        ],
        Null
    ];
    l
]


Normal[l_Cons] ^:= ToList[l]


LazyEval[Cons[], ___] := Cons[]
LazyEval[l_Cons, n_Integer : 1] := Fold[
    MapAtInplace[Evaluate, #1, #2] &,
    Unevaluated[l],
    Catenate[With[{t = Table[2, #]}, {Append[t, 1], Append[t, 2]}] & /@ Range[0, n - 1]]
]
LazyEval[n_Integer : 1][l_Cons] := LazyEval[l, n]


LazyListQ = MatchQ[_Cons];


LazyListForm[Cons[]] := {}
LazyListForm[Cons[x_, Cons[]]] := {Interpretation[Shallow[Defer @ x, {5, 5}], x]}
LazyListForm[Cons[x_, l_]] := {
    Interpretation[Shallow[Defer @ x, {5, 5}], x],
    Replace[LazyListForm[Unevaluated @ l], list_List :> Splice @ list]
}
LazyListForm[thunk : head_[___] | head_] := Interpretation[Framed @ Shallow[Defer @ thunk, {5, 5}], LazyListForm[thunk]]


Format[l_Cons] := LazyListForm[l]

