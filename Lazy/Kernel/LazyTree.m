Package["Wolfram`Lazy`"]

PackageExport["LazyTree"]
PackageExport["LazyTreeRuleForm"]
PackageExport["LazyTreeForm"]
PackageExport["ConsTree"]
PackageExport["LazyNestTree"]
PackageExport["LazyTreeToTree"]


SetAttributes[LazyTree, HoldAll]

LazyTree[x_] := LazyTree[x, LazyList[]]


LazyTreeToTree[LazyTree[data_, children_]] ^:= CheckAbort[
    If[ Length[Stack[]] >= $RecursionLimit - 2,
        Tree[data, None],
        Tree[data, LazyTreeToTree /@ LazyListToList[children]]
    ],
    Tree[data, None]
]
LazyTreeToTree[x_] := x


TreeData[LazyTree[data_, _]] ^:= data
TreeChildren[LazyTree[_, children_]] ^:= children

TreeExtract[t_LazyTree, h_[]] ^:= t
TreeExtract[t_LazyTree, h_[p_, s___]] /; FlatQ[h] ^:= Lazy @ TreeExtract[LazyPart[TreeChildren[t], p], s]
TreeExtract[t_LazyTree, h_[p_, s_]] ^:= Lazy @ TreeExtract[LazyPart[TreeChildren[t], p], s]
TreeExtract[t_LazyTree, h_[l_]] ^:= Lazy @ TreeExtract[t, l]


LazyTreeRuleForm[LazyTree[data_, l : _Cons | _LazyList]] := data -> l
LazyTreeRuleForm[LazyTree[data_, l_]] := data -> LazyValue[l]
(* LazyTreeRuleForm[x_] := x *)


treeOpts = {AspectRatio -> 1 / 2}
LazyTreeForm[LazyTree[data_, l_LazyList]] := Tree[data,
    Append[LazyTreeForm /@ ConsForm[Unevaluated[l]], With[{r = ConsLast[l]}, If[r === LazyList[], Nothing, Tooltip["\[Ellipsis]", InputForm[r]]]]],
    treeOpts
]
LazyTreeForm[LazyTree[data_, l_]] := Tree[data,
    {Tooltip["\[Ellipsis]", InputForm[l]]},
    treeOpts
]
LazyTreeForm[l_LazyList] :=
    Append[LazyTreeForm /@ ConsForm[Unevaluated[l]], With[{r = ConsLast[l]}, If[r === LazyList[], Nothing, Tooltip[Framed["\[Ellipsis]"], InputForm[r]]]]]
LazyTreeForm[x_] := Tooltip["\[Ellipsis]", InputForm[x]]


ConsTree[h_[x_, l_]] := LazyTree[h, h[x, h[ConsTree[l], h[]]]]
ConsTree[h_[]] := LazyTree[h]
ConsTree[x_] := x


LazyNestTree[_, x_, 0] := LazyTree[x, LazyList[]]
LazyNestTree[f_, x_, n : (_Integer ? NonNegative) | Infinity : Infinity] := LazyTree[x, LazyValue[LazyNestTree[f, #, n - 1] & /@ ToLazyList[f[x]]]]


Format[t_LazyTree] ^:= LazyTreeRuleForm[t]


Part[t_LazyTree, p___] ^:= LazyPart[t, p]

