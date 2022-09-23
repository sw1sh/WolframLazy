Package["Wolfram`Lazy`"]

PackageExport["LazyTree"]
PackageExport["LazyTreeQ"]
PackageExport["LazyTreeData"]
PackageExport["LazyTreeChildren"]
PackageExport["LazyTreeRuleForm"]
PackageExport["LazyTreeForm"]
PackageExport["LazyTreeSubtree"]
PackageExport["ConsTree"]
PackageExport["LazyNestTree"]
PackageExport["LazyTreeToTree"]
PackageExport["LazyTreeEdges"]


LazyTreeQ[t_] := MatchQ[t, LazyTree[_, _]]


SetAttributes[LazyTree, HoldAll]

l_LazyTree /; $LazyNoEntry && System`Private`EntryQ[Unevaluated[l]] := System`Private`SetNoEntry[Unevaluated[l]]

LazyTree[x_] := LazyTree[x, LazyList[]]


LazyTreeToTree[LazyTree[data_, children_], opts___] ^:= Block[{
	tree = Tree[ReleaseLazyValue[data], {}],
	cs = {ReleaseLazyValue[children]},
	pos = {{ {1} }},
	i
},
    CheckAbort[
        While[cs =!= {},
            i = 1;
            Scan[AbortProtect[
                LazyScan[
                    (
						If[	LazyTreeQ[#],
                        	tree = TreeInsert[tree, Tree[ReleaseLazyValue[TreeData[#]], {}], Last[pos[[i]]]];
							AppendTo[cs, ReleaseLazyValue[TreeChildren[#]]],

							tree = TreeInsert[tree, Tree[ReleaseLazyValue[#], {}], Last[pos[[i]]]];
							AppendTo[cs, {}]
						];
						AppendTo[pos[[i]], MapAt[# + 1 &, Last[pos[[i]]], -1]];
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
LazyTreeForm[LazyTree[data_, l_LazyList], opts___] := Tree[data,
    Append[LazyTreeForm[#, opts] & /@ LazyListSublist[Unevaluated[l]], With[{r = ConsLast[l]}, If[r === LazyList[], Nothing, Tooltip["\[Ellipsis]", InputForm[r]]]]],
    opts,
    treeOpts
]
LazyTreeForm[LazyTree[data_, l_], opts___] := Tree[data,
    {Tooltip["\[Ellipsis]", InputForm[l]]},
    opts,
    treeOpts
]
LazyTreeForm[l_LazyList, opts___] :=
    Append[LazyTreeForm[#, opts] & /@ LazyListSublist[Unevaluated[l]], With[{r = ConsLast[l]}, If[r === LazyList[], Nothing, Tooltip[Framed["\[Ellipsis]"], InputForm[r]]]]]
LazyTreeForm[x_] := Tooltip["\[Ellipsis]", InputForm[x]]


LazyTreeSubtree[LazyTree[data_, l_LazyList], opts___] := Tree[data, LazyTreeSubtree[#, opts] & /@ LazyListSublist[Unevaluated[l]], opts, treeOpts]
LazyTreeSubtree[LazyTree[data_, l_], opts___] := Tree[data, None, opts, treeOpts]
LazyTreeSubtree[l_LazyList, opts___] := LazyTreeSubtree[#, opts] & /@ LazyListSublist[Unevaluated[l]]
LazyTreeSubtree[x_] := x


ConsTree[h_[x_, l_]] := LazyTree[h, h[x, h[ConsTree[l], h[]]]]
ConsTree[h_[]] := LazyTree[h]
ConsTree[x_] := x


LazyNestTree[_, x_, 0] := LazyTree[x, LazyList[]]
LazyNestTree[f_, x_, n : (_Integer ? NonNegative) | Infinity : Infinity] := LazyTree[x, LazyValue[LazyNestTree[f, #, n - 1] & /@ ToLazyList[f[x]]]]


LazyTree /: MakeBoxes[l_LazyTree, form_] := With[{
    icon = With[{tree = UnlabeledTree[LazyTreeSubtree[l], ImageSize -> Tiny]},
		If[MatchQ[TreeChildren[tree], {} | None], Graphics[Point[{0, 0}]], tree]
	]
},
    BoxForm`ArrangeSummaryBox[
        "LazyTree",
        l,
        icon,
        {{}},
        {{}},
        form,
		"Interpretable" -> Automatic
	]
]


Part[t_LazyTree, p___] ^:= LazyPart[t, p]



(* LazyTreeEdges *)

Options[LazyTreeEdges] = {"TraversalOrder" -> "BreadthFirst", "Deterministic" -> True, "Nested" -> False};

LazyTreeEdges[l : _LazyList | _LazyTree, OptionsPattern[]] := With[{
	traversalOrder = OptionValue["TraversalOrder"],
	deterministicQ = TrueQ[OptionValue["Deterministic"]],
	nestedQ = TrueQ[OptionValue["Nested"]]
},
	If[nestedQ, Identity, LazyCatenate] @ If[
		deterministicQ,
		LazyTreeEdgesDeterministic[l, traversalOrder],
		LazyTreeEdgesNonDeterministic[l, traversalOrder]
	]
]


LazyTreeEdgesNonDeterministic[l_LazyList, "BreadthFirst"] := With[{
	trees = LazySelect[# =!= Nothing &] @ LazyMap[
		Replace[{
			LazyTree[x_, cs_] :> With[{v = Replace[x, Labeled[v_, _] :> v]},
				If[MemberQ[fs, v], Nothing, LazyTree[v, cs]]
			],
			_ -> Nothing
		}],
		l
	]
},
With[{
	edges = LazyCatenate @ LazyMap[Replace[LazyTree[v_, cs_] :> LazySelect[# =!= Nothing &] @
        LazyMap[Replace[{LazyTree[Labeled[w_, tag_] | w_, _] :> DirectedEdge[v, Sequence[w, tag]], _ -> Nothing}], cs]],
        trees
    ]
},
	LazyList[
		edges,
		LazyTreeEdgesNonDeterministic[ReleaseLazyValue @ LazyCatenate @ LazyMap[Replace[LazyTree[_, cs_] :> cs], trees]]
	]
]]

LazyTreeEdgesNonDeterministic[t_LazyTree, "BreadthFirst"] := LazyTreeEdgesNonDeterministic[LazyList[t, LazyList[]]]


LazyTreeEdgesNonDeterministic[LazyTree[x_, c_], "DepthFirst"] := With[{
	v = Replace[x, Labeled[v_, _] :> v],
	cs = ReleaseLazyValue @ c
},
	If[ cs === LazyList[],
		LazyList[],
		With[{first = ReleaseLazyValue @ LazyFirst[cs]},
		With[{edges =
			Replace[first, {
				t : LazyTree[y_, _] :> With[{w = Replace[y, Labeled[w_, _] :> w], edge = DirectedEdge[v, Replace[y, Labeled[w_, l_] :> Sequence[w, l]]]},
					With[{fibrations = LazyValue @ LazyTreeEdgesNonDeterministic[t, "DepthFirst"]},
						LazyList[LazyPrepend[edge] @ LazyFirst[fibrations, LazyList[]], LazyRest[fibrations, LazyList[]]]
					]
				],
				_ -> LazyList[]
			}]
		},
			LazyJoin[
				edges,
				LazyValue @ LazyTreeEdgesNonDeterministic[LazyTree[v, ReleaseLazyValue @ LazyRest[cs]]]
			]
		]
		]
	]
]

LazyTreeEdgesNonDeterministic[LazyList[]] := LazyList[]
LazyTreeEdgesNonDeterministic[l_LazyList, "DepthFirst"] := With[{
	edges = LazyTreeEdgesNonDeterministic[ReleaseLazyValue @ LazyFirst[l, LazyList[]]]
},
	LazyJoin[
		edges,
		LazyTreeEdgesNonDeterministic[ReleaseLazyValue @ LazyRest[l, LazyList[]]. "DepthFirst"]
	]
]

LazyTreeEdgesNonDeterministic[l_] := LazyTreeEdgesNonDeterministic[l, "BreadthFirst"]

LazyTreeEdgesNonDeterministic[__] := LazyList[]


LazyTreeEdgesDeterministic[l_, order_String : "BreadthFirst"] := Switch[order, "BreadthFirst", LazyTreeFoliationEdges[l], _, LazyTreeFibrationEdges[l]]
LazyTreeEdgesDeterministic[__] := LazyList[]


LazyTreeFoliationEdges[t_LazyTree, foliation_LazyList : LazyList[]] := LazyTreeFoliationEdges[LazyList[t, LazyList[]], foliation]

LazyTreeFoliationEdges[LazyList[], _] := LazyList[]
LazyTreeFoliationEdges[l_LazyList, foliation_LazyList : LazyList[]] := With[{fs = Normal @ foliation}, With[{
	trees = LazySelect[# =!= Nothing &] @ LazyMap[
		Replace[{
			LazyTree[x_, cs_] :> With[{v = Replace[x, Labeled[v_, _] :> v]},
				If[MemberQ[fs, v], Nothing, LazyTree[v, cs]]
			],
			_ -> Nothing
		}],
		l
	]
},
With[{
	edges = LazyDeleteDuplicates @ LazyCatenate @ LazyMap[Replace[LazyTree[v_, cs_] :> LazySelect[# =!= Nothing &] @
        LazyMap[Replace[{LazyTree[Labeled[w_, tag_] | w_, _] :> DirectedEdge[v, Sequence[w, tag]], _ -> Nothing}], cs]],
        trees
    ]
},
	LazyList[
		edges,
		LazyTreeFoliationEdges[
			ReleaseLazyValue @ LazyDeleteDuplicatesBy[Replace[LazyTree[Labeled[w_, _] | w_, _] :> w]] @ LazyCatenate @ LazyMap[Replace[LazyTree[_, cs_] :> cs], trees],
			ReleaseLazyValue @ LazyJoin[foliation, LazyMap[#[[1]] &, edges]]
		]
	]
]]]
LazyTreeFoliationEdges[__] := LazyList[]


LazyTreeFibrationEdges[LazyTree[x_, c_], fibration_LazyList : LazyList[]] := With[{
	v = Replace[x, Labeled[v_, _] :> v],
	cs = ReleaseLazyValue @ LazyDeleteDuplicatesBy[Replace[TreeData[#], Labeled[e_, _] :> e] &] @ c
},
	If[ cs === LazyList[],
		LazyList[],
		With[{first = ReleaseLazyValue @ LazyFirst[cs]},
		With[{edges =
			Replace[first, {
				t : LazyTree[y_, _] :> With[{w = Replace[y, Labeled[w_, _] :> w], edge = DirectedEdge[v, Replace[y, Labeled[w_, l_] :> Sequence[w, l]]]},
					If[ w === v || ReleaseLazyValue @ LazyMemberQ[fibration, w],
						LazyList[LazyList[edge], LazyList[]],
						With[{fibrations = LazyValue @ LazyTreeFibrationEdges[t, LazyPrepend[fibration, v]]},
							LazyList[LazyPrepend[edge] @ LazyFirst[fibrations, LazyList[]], LazyRest[fibrations, LazyList[]]]
						]
					]
				],
				_ :> LazyList[]
			}]
		},
			LazyJoin[
				edges,
				LazyValue @ LazyTreeFibrationEdges[LazyTree[v, ReleaseLazyValue @ LazyRest[cs]], ReleaseLazyValue @ LazyDeleteDuplicates @ LazyJoin[fibration, LazyMap[#[[2]] &, LazyCatenate @ edges]]]
			]
		]
		]
	]
]

LazyTreeFibrationEdges[LazyList[], _] := LazyList[]
LazyTreeFibrationEdges[l_LazyList, fibration_LazyList : LazyList[]] := With[{
	edges = LazyTreeFibrationEdges[ReleaseLazyValue @ LazyFirst[l, LazyList[]], fibration]
},
	LazyJoin[
		edges,
		LazyTreeFibrationEdges[ReleaseLazyValue @ LazyRest[l, LazyList[]], ReleaseLazyValue @ LazyDeleteDuplicates @ LazyJoin[fibration, LazyMap[#[[2]] &, LazyCatenate @ edges]]]
	]
]
LazyTreeFibrationEdges[__] := LazyList[]