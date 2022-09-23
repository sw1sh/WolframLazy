Package["Wolfram`Lazy`"]

PackageExport["LazyPart"]
PackageExport["MultiwayNest"]
PackageExport["LazyTraverse"]
PackageExport["LazyTreePath"]
PackageExport["LazyDirectoryTree"]



LazyPart[t_LazyTree, _[]] := t
LazyPart[LazyTree[_, l_] | l_, h_[p_, ps___]] /; FlatHoldQ[h] := LazyValue @ LazyPart[LazyPart[l, p], ArgEval[h[ps]]]
LazyPart[LazyTree[_, l_] | l_, h_[p_, ps_]] /; HoldQ[h] := LazyValue @ LazyPart[LazyPart[l, p], ps]
LazyPart[t_LazyTree, h_[p_]] /; HoldFirstQ[h] := h @ LazyPart[t, p]
LazyPart[LazyTree[_, l_] | l_, p_Integer ? Positive, ps___] := LazyPart[LazyFirst[LazyDrop[l, p - 1], Missing[p]], ps]
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


Options[LazyTraverse] = {TimeConstraint -> 1, "MaxUniqueNodes" -> Infinity, "MaxNodes" -> Infinity, "TraversalOrder" -> "Random", "Deterministic" -> True}
LazyTraverse[initLazy_ ? LazyQ, patt_, initPos_Association, initVisited_List, prop_String, opts : OptionsPattern[]] := Block[{
	$LazyNoEntry = False,
    lazy, pos = initPos, visited = initVisited, p, pp, found,
    timeConstraint = OptionValue[TimeConstraint],
	traversalOrder = OptionValue["TraversalOrder"],
	maxNodes = OptionValue["MaxNodes"],
	maxVisited = OptionValue["MaxUniqueNodes"],
	deterministicQ = TrueQ[OptionValue["Deterministic"]],
	nodeCount = 0
},
	CheckAbort[
		lazy = ReleaseHold @ HoldAtom[initLazy];
		TimeConstrained[
			While[
				!ValueQ[found] && Length[pos] > 0 && Length[visited] < maxVisited && nodeCount < maxNodes,
				AbortProtect[
				pos = Switch[traversalOrder,
					"DepthFirst",
					pos = LexicographicSort[pos],
					"BreadthFirst",
					pos = Sort[pos,
						If[Length[#1] == Length[#2], LexicographicOrder[#1, #2], Order[Length[#1], Length[#2]]] &],
					_,
					RandomSample[pos]
				];
				p = First[Keys[pos]];
				pp = First[pos];
				lazy[[Sequence @@ p]] = Replace[
					First[Extract[lazy, {p}, Hold]],
					{
						Hold[LazyTree[x_, l_]] :> With[{z = ReleaseLazyValue[x]},
							If[ MatchQ[z, patt], found = pp];
							If[ !deterministicQ || !MemberQ[visited, z],
								AppendTo[pos, Append[p, 2] -> Append[pp, 1]];
								AppendTo[visited, z]
							];
							pos = Rest[pos];
							nodeCount++;
							LazyTree[z, l]
						],
						Hold[LazyList[x_, l_]] :> With[{z = ReleaseLazyValue[x]},
							If[	MatchQ[z, patt],
								found = pp,
								AppendTo[pos, Append[p, 1] -> pp]
							];
							AppendTo[pos, Append[p, 2] -> MapAt[# + 1 &, pp, -1]];
							pos = Rest[pos];
							LazyList[z, l]
						],
						Hold[x : LazyList[]] :> (pos = Rest[pos]; x),
						Hold[LazyValue[x_] | x_] :> x
					}
				];
				]
			],
        	timeConstraint
    	],
        Null
    ];
	With[{computation = LazyComputation[<|
			"Lazy" -> System`Private`SetNoEntry[lazy],
			"Position" -> pos,
			"Paths" -> If[ValueQ[found], {found}, {}],
			"Visited" -> visited,
			"Pattern" -> patt,
			Method -> "LazyTraverse",
			"Options" -> {opts}
		|>]},

		If[	prop === "Computation" || !MemberQ[computation["Properties"], prop],
			computation,
			computation[prop]
		]
	]
]

LazyTraverse[initLazy_ ? LazyQ, patt_, prop_String, opts : OptionsPattern[]] :=
	LazyTraverse[initLazy, patt, <|{} -> If[MatchQ[initLazy, _LazyTree], {}, {1}]|>, {}, prop, opts]
LazyTraverse[initLazy_ ? LazyQ, prop_String : "Lazy", opts : OptionsPattern[]] :=
	LazyTraverse[initLazy, Alternatives[], prop, opts]
LazyTraverse[initLazy_ ? LazyQ, patt_, opts : OptionsPattern[]] :=
	LazyTraverse[initLazy, patt, "Lazy", opts]
LazyTraverse[patt_ : Alternatives[]][initLazy_ ? LazyQ, args___] := LazyTraverse[initLazy, patt, args]

ConsToListPosition[{}, lazy_] := {}
ConsToListPosition[pos : {x : 1 | 2, xs : (1 | 2) ...}, lazy : h_[y_, ys_]] :=
	Switch[x, 1, Switch[h, LazyList, Prepend[ConsToListPosition[{xs}, y], x], LazyTree, {}], 2, Switch[h, LazyList, MapAt[# + 1 &, ConsToListPosition[{xs}, ys], 1], LazyTree, ConsToListPosition[{xs}, ys]]]

LazyTreePath[l_, path : {_Integer...}] := TreeData[l[[##]]] & @@@ FoldList[Append, {}, path]
LazyTreePath[l_, paths : {{_Integer...}...}] := LazyTreePath[l, #] & /@ paths

LazyTreePath[l_, path_LazyList] := TreeData /@ TakeWhile[LazyPart[l, #] & /@ FoldList[Append, LazyList[], path], LazyTreeQ]


LazyDirectoryTree[dir_] := LazyTree[Tooltip[FileBaseName[dir], dir], LazyDirectoryTree /@ LazyList @ FileNames[All, dir]]

