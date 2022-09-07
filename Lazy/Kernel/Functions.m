Package["Wolfram`Lazy`"]

PackageExport["LazyPart"]
PackageExport["MultiwayNest"]
PackageExport["LazyFindPath"]


LazyPart[LazyValue[x_], ps___] := LazyValue[LazyPart[x, ps]]
LazyPart[t_LazyTree, _[]] := t
LazyPart[LazyTree[_, l_] | l_, h_[p_, ps___]] /; FlatHoldQ[h] := LazyValue @ LazyPart[LazyPart[l, p], ArgEval[h[ps]]]
LazyPart[LazyTree[_, l_] | l_, h_[p_, ps_]] /; HoldQ[h] := LazyValue @ LazyPart[LazyPart[l, p], ps]
LazyPart[t_LazyTree, h_[p_]] /; HoldFirstQ[h] := h @ LazyPart[t, p]
LazyPart[LazyTree[_, l_] | l_, p_Integer ? Positive, ps___] := LazyPart[ReleaseLazyValue @ LazyFirst[LazyDrop[l, p - 1], Missing[p]], ps]
LazyPart[x_] := x

LazyPart[l_, from_Integer ? Positive ;; to_Integer ? Positive] /; to >= from := LazyTake[LazyDrop[l, from - 1], to - from + 1]
LazyPart[h_[___], from_Integer ? Positive ;; to_Integer ? Positive] := h[]


MultiwayNest[f_, l_, _ ? Negative, "BreadthFirst"] := LazyList[]
MultiwayNest[f_, l_, n : _Integer ? NonNegative | Infinity : Infinity, "BreadthFirst"] := With[{xs = ToLazyList[l]},
    If[ xs === LazyList[],
        LazyList[],
        With[{
            edges = LazyCatenate @ LazyMap[x |-> LazyMap[DirectedEdge[x, #] &, ToLazyList[f[x]]], xs]
        },
            LazyTake[LazyJoin[edges, LazyValue @ MultiwayNest[f, LazyMap[#[[2]] &, edges], "BreadthFirst"]], n]
        ]
    ]
]
MultiwayNest[f_, l_, n : _Integer ? NonNegative | Infinity : Infinity, "DepthFirst"] := With[{xs = ToLazyList[l]},
	If[ xs === LazyList[],
		LazyList[],
		With[{x = ReleaseLazyValue[LazyFirst[xs]], rest = LazyRest[xs]},
		With[{ys = ToLazyList[f[x]]},
		If[
			ys === LazyList[],
			LazyValue @ MultiwayNest[f, rest, "DepthFirst"],
			With[{y = ReleaseLazyValue[LazyFirst[ys]], zs = LazyRest[ys]},
				LazyTake[
                    LazyJoin[
                        LazyList[x \[DirectedEdge] y, MultiwayNest[f, y, "DepthFirst"]],
                        LazyCatenate @ LazyMap[LazyList[DirectedEdge[x, #], MultiwayNest[f, #, "DepthFirst"]] &, zs],
                        LazyValue @ MultiwayNest[f, rest, "DepthFirst"]
                    ],
                    n
                ]
			]
		]]]
	]
]
MultiwayNest[f_, l_, "NestedList"] := With[{xs = ToLazyList[l]},
    If[ xs === LazyList[],
        LazyList[],
        With[{
            edges = LazyMap[x |-> LazyMap[DirectedEdge[x, #] &, ToLazyList[f[x]]], xs]
        },
            LazyJoin[edges, LazyValue @ LazyMap[MultiwayNest[f, #[[2]], "NestedList"] &, LazyCatenate @ edges]]
        ]
    ]
]
MultiwayNest[f_, l_, "Tree" | "Trees"] := With[{xs = ToLazyList[l]},
    If[ xs === LazyList[],
        LazyTree[],
        LazyMap[LazyTree[#, LazyCatenate @ LazyMap[MultiwayNest[f, #, "Tree"] &, ToLazyList[f[#]]]] &, xs]
    ]
]

MultiwayNest[args : PatternSequence[___, Except[_String]]] := MultiwayNest[args, "Tree"]

ResourceFunction["AddCodeCompletion"][MultiwayNest, {None, None, "BreadthFirst", "DepthFirst", "NestedList", "Tree"}]


Options[LazyFindPath] = {TimeConstraint -> 5, "TraversalOrder" -> "Random"}
LazyFindPath[initLazy_, patt_, initPos_Association, initVisited_List, opts : OptionsPattern[]] := Block[{
    lazy = initLazy, pos = initPos, visited = initVisited, p, pp, found,
    timeConstraint = OptionValue[TimeConstraint],
	traversalOrder = OptionValue["TraversalOrder"]
},
	CheckAbort[TimeConstrained[While[!ValueQ[found] && Length[pos] > 0,
		AbortProtect[
        pos = Switch[traversalOrder,
			"DepthFirst",
			pos = LexicographicSort[pos],
			"BreadthFirst",
			pos = SortBy[pos, Length, LexicographicOrder],
			_,
			RandomSample[pos]
		];
		p = First[Keys[pos]];
		pp = First[pos];
		lazy[[Sequence @@ p]] = Replace[
			First[Extract[lazy, {p}]],
			{
				LazyTree[x_, l_] :> With[{z = ReleaseLazyValue[x]},
					If[ MatchQ[z, patt], found = Most[pp]];
					If[ !MemberQ[visited, z],
						If[ Unevaluated[l] =!= LazyList[],
							AppendTo[pos, Append[p, 2] -> pp]
						];
						AppendTo[visited, z]
					];
					pos = Rest[pos];
					LazyTree[z, l]
				],
				LazyList[x_, l_] :> With[{z = x},
					If[	MatchQ[z, patt],
						found = pp,
						AppendTo[pos, Append[p, 1] -> Append[pp, 1]]
					];
					If[ Unevaluated[l] =!= LazyList[],
						AppendTo[pos, Append[p, 2] -> MapAt[# + 1 &, pp, -1]]
					];
					pos = Rest[pos];
					LazyList[z, l]
				],
				x : LazyList[] :> (pos = Rest[pos]; x),
				LazyValue[x_] :> With[{z = x},
					If[MatchQ[z, patt], found = Most[pp]];
                    (* AppendTo[visited, z]; *)
					z
				]
			}
		]
		]
	],
        timeConstraint
    ],
        Null
    ];

	LazyComputation[<|
        "Lazy" -> lazy,
        "Position" -> pos,
        "Paths" -> If[ValueQ[found], {found}, {}],
        "Visited" -> visited,
        "Pattern" -> patt,
        Method -> "FindPath",
        "Options" -> {opts}
    |>]
]
LazyFindPath[initLazy_, patt_, opts : OptionsPattern[]] :=
	LazyFindPath[initLazy, patt, <|{} -> If[MatchQ[initLazy, _LazyTree], {}, {1}]|>, {}, opts]


ConsToListPosition[{}, lazy_] := {}
ConsToListPosition[pos : {x : 1 | 2, xs : (1 | 2) ...}, lazy : h_[y_, ys_]] :=
	Switch[x, 1, Switch[h, LazyList, Prepend[ConsToListPosition[{xs}, y], x], LazyTree, {}], 2, Switch[h, LazyList, MapAt[# + 1 &, ConsToListPosition[{xs}, ys], 1], LazyTree, ConsToListPosition[{xs}, ys]]]

