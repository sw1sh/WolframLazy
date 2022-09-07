Package["Wolfram`Lazy`"]

PackageExport["LazyTree"]
PackageExport["LazyTreeData"]
PackageExport["LazyTreeChildren"]
PackageExport["LazyTreeRuleForm"]
PackageExport["LazyTreeForm"]
PackageExport["ConsTree"]
PackageExport["LazyNestTree"]
PackageExport["LazyTreeToTree"]


SetAttributes[LazyTree, HoldAll]

LazyTree[x_] := LazyTree[x, LazyList[]]


LazyTreeToTree[LazyTree[data_, children_], opts___] ^:= Block[{tree = Tree[data, {}], cs = {children}, pos = {{ {1} }}, i},
    CheckAbort[
        While[cs =!= {},
            i = 1;
            Scan[AbortProtect[
                LazyScan[
                    (
                        tree = TreeInsert[tree, Tree[TreeData[#], {}], Last[pos[[i]]]];
                        AppendTo[pos[[i]], MapAt[# + 1 &, Last[pos[[i]]], -1]];
                        AppendTo[cs, TreeChildren[#]]
                    ) &,
                    #
                ];
                pos[[i]] = Most[pos[[i]]];
                cs = Rest[cs];
                i++
                ] &,
                cs
            ];
            pos = Catenate @ Map[List @* Append[1], pos, {2}];
        ],
        Null
    ];
    Tree[tree, opts, AspectRatio -> 1 / 3]
]
LazyTreeToTree[x_] := x


LazyTreeData[LazyTree[data_, _]] ^:= data
LazyTreeData[v_LazyValue] := LazyTreeData[ReleaseLazyValue[v]]
LazyTreeChildren[LazyTree[_, children_]] ^:= children
LazyTreeChildren[v_LazyValue] := LazyTreeChildren[ReleaseLazyValue[v]]

TreeData[t_LazyTree] ^:= LazyTreeData[t]
TreeData[t_LazyValue] ^:= LazyTreeData[t]
TreeChildren[t_LazyTree] ^:= LazyTreeChildren[t]
TreeChildren[t_LazyValue] ^:= LazyTreeChildren[t]


LazyTree /: TreeExtract[t_LazyTree, p_List] := TreeExtract[t, LazyList[p]]
TreeExtract[t_LazyTree, h_[]] ^:= t
TreeExtract[t_LazyTree, h_[p_, s___]] /; FlatQ[h] ^:= LazyValue @ TreeExtract[LazyPart[TreeChildren[t], p], s]
TreeExtract[t_LazyTree, h_[p_, s_]] ^:= LazyValue @ TreeExtract[LazyPart[TreeChildren[t], p], s]
TreeExtract[t_LazyTree, h_[l_]] ^:= LazyValue @ TreeExtract[t, l]


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

