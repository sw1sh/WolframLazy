Package["Wolfram`Lazy`"]

PackageImport["Wolfram`Patterns`"]

PackageExport["MakeExprStruct"]
PackageExport["MakeExprStructHold"]
PackageExport["WithExprStruct"]
PackageExport["WithExprStructHold"]
PackageExport["Spliced"]

PackageExport["LazyExpression"]
PackageExport["LazyExpressionRefQ"]
PackageExport["LazyExpressionQ"]
PackageExport["LazyExpressionEvaluate"]
PackageExport["$LazyExpressionSymbols"]
PackageExport["$LazyExpressionCache"]
PackageExport["ClearLazyCache"]



$LazyExpressionCache = False

$LazyExpressionSymbols = {}

ClearLazyCache[] := (Unprotect @@@ $LazyExpressionSymbols; ClearAll @@@ $LazyExpressionSymbols; Remove @@@ $LazyExpressionSymbols; ClearAll[Wolfram`Lazy`LazyExpression]; Get["Wolfram`Lazy`"])


MakeExprStruct[expr_] := CreateDataStructure["ExprStruct", HoldComplete[expr]]["Part", 1]
MakeExprStruct[expr___] := CreateDataStructure["ExprStruct", HoldComplete[Sequence[expr]]]["Part", 1]
MakeExprStructHold[expr___] := Function[Null, MakeExprStruct[##], HoldAllComplete] @@ Unevaluated /@ HoldComplete[expr]
SetAttributes[MakeExprStructHold, HoldAllComplete]

WithExprStruct[expr_] := With[{holdExpr = HoldComplete[expr]}, With[{pos = Position[holdExpr, ds_DataStructure /; DataStructureQ[ds, "ExprStruct"]]},
	With[{subExprs = Flatten[HoldComplete @@ Extract[holdExpr, pos, #["ConstructWith", HoldComplete]["Get"] &], 1, HoldComplete]},
		CreateDataStructure["ExprStruct", ReplacePart[holdExpr, List @@ Thread[HoldComplete @@ pos :> subExprs, HoldComplete]]]["Part", 1]
	]
]]
WithExprStructHold[expr_] := WithExprStruct[Unevaluated[expr]]
SetAttributes[WithExprStructHold, HoldAllComplete]

(* Functions *)

Spliced[f_][left___, Splice[l_], right___] := Splice[Lazy[Map][Spliced[f][left, #, right] &, l]]
Spliced[f_][args___] := f[args]

SetSplice[head_] := With[{headRHS = head /. Verbatim[Pattern][name_, _] :> name},
    SetDelayed @@ Hold[head[left___, {Splice[l_], rest___}, right___], headRHS[left, Lazy[Join][l, {rest}], right]]
]

Scan[SetSplice, {Lazy[First], Lazy[Rest], Lazy[Prepend][x_], Lazy[Map][f_], Lazy[Select], Lazy[FoldList], Lazy[Take], Lazy[Part]}]

Lazy[Length][l_List] := Length[l]

Lazy[First][{x_, ___}] := x
Lazy[First][{}, def_] := def

Lazy[Rest][{_, rest___}] := {rest}
Lazy[Rest][{}, def_] := def

Lazy[Prepend][x_][{rest___}] := {x, rest}
Lazy[Prepend][l_, x_] := Lazy[Prepend][x][l]

Lazy[Join][x_] := x
Lazy[Join][ls___List] := Join[ls]
Lazy[Join][left___, {}, right___] := Lazy[Join][left, right]
Lazy[Join][{xs___}, rest___] := {xs, Splice[Splice /@ {rest}]}

Lazy[Map][_][{}] := {}
(* Lazy[Map][f_Symbol][{xs : Longest[Except[_Splice] ...], rest___}] /; MemberQ[Attributes[f], Listable] := Lazy[Join][f[{xs}], Lazy[Map][f, {rest}]] *)
Lazy[Map][f_][{x_, rest___}] := {f[x], Splice[Lazy[Map][f][{rest}]]}
Lazy[Map][f_, l_List] := Lazy[Map][f][l]

Lazy[Select][{}, _] := {}
Lazy[Select][{x_, rest___}, crit_] := If[crit[x], {x, Splice[Lazy[Select][{rest}, crit]]}, Lazy[Select][{rest}, crit]]

Lazy[MapThread][f_, l : {{__}...}] := With[{firsts = Lazy[First] /@ l, rests = Lazy[Rest] /@ l},
    {f @@ firsts, Splice[Lazy[MapThread][f, rests]]}
]
Lazy[MapThread][_, {___, {}, ___}] := {}

Lazy[FoldList][f_, x_, {y_, ys___}] := With[{z = f[x, y]}, {x, Splice[Lazy[FoldList][f, z, {ys}]]}]
Lazy[FoldList][f_, {y_, ys___}] := Lazy[FoldList][f, y, {ys}]
Lazy[FoldList][_, x_, {}] := {x}

Lazy[Take][_, n_Integer /; n <= 0] := {}
Lazy[Take][{xs : Longest[Except[_Splice] ...], rest___}, n_Integer] := With[{l = Length[{xs}]}, If[n <= l, Take[{xs}, n], Lazy[Join][{xs}, Lazy[Take][{rest}, n - l]]]]
Lazy[Take][{}, _] := {}

Lazy[Part][{x_, ___}, 1] := x
Lazy[Part][{_, rest___}, n_Integer ? Positive] := Lazy[Part][{rest}, n - 1]
Lazy[Part][l, 1 ;; to_] := Lazy[Take][l, to]
Lazy[Part][_, from_Integer ;; to_Integer] /; from > to := {}
Lazy[Part][{_, rest___}, from_Integer ? Positive ;; to_] := Lazy[Part][{rest}, from + 1 ;; to]


Scan[SetSplice, {evens, odds, merge}]

evens[{}] := {}
evens[{_, right___}] := odds[{right}]

odds[{}] := {}
odds[{x_, right___}] := {x, Splice[evens[{right}]]}

cleave[xs_] := {evens[xs], odds[xs]}

merge[xs_, {}] := xs
merge[{}, ys_] := ys
merge[xs : {x_, t___}, ys: {y_, u___}] := WithExprStructHold[If[x <= y // EchoEvaluation, {x, Splice[merge[{t}, ys]]}, {y, Splice[merge[xs, {u}]]}]]

Lazy[Sort][{}] := {}
Lazy[Sort][{x_}] := {x}
Lazy[Sort][xs_] := Replace[cleave[xs], {e_, o_} :> WithExprStructHold[merge[Lazy[Sort][e], Lazy[Sort][o]]]]


LazyExpressionHold[expr_] := WithExprStructHold @@ ReplaceAll[HoldComplete[expr], Verbatim[LazyExpression][ref_Symbol] /; LazyExpressionRefQ[Unevaluated[ref]] :> ref]

Part[l_LazyExpression, part___] ^:= WithExprStructHold[Lazy[Part][l, part]]
Map[f_, l_LazyExpression] ^:= WithExprStructHold[Lazy[Map][f, l]]
Select[l_LazyExpression, crit_] ^:= WithExprStructHold[Lazy[Select][l, crit]]
Take[l_LazyExpression, arg_] ^:= WithExprStructHold[Lazy[Take][l, arg]]

(* Generators *)

$LazyExpressionGenerators = {Range, NestList, Table}

Scan[
    Function[Lazy[#][args__] := With[{ds = Lazy[#, args]},
        LazyExpression[ds]
    ]],
    $LazyExpressionGenerators
]

Lazy[Range][] := Lazy[Range][1, Infinity]
Lazy[Range][args___] := LazyExpression[#] & @ Lazy[Range, args]
Lazy[Range, from_, to_, step_ : 1] := If[
    from - step == to,
    {},
    With[{next = from + step},
        MakeExprStructHold[{from, Splice @ Lazy[Range, next, to, step]}]
    ]
]
Lazy[Range, to_] := Lazy[Range, 1, to]

Lazy[NestList][args___] := LazyExpression[#] & @ Lazy[NestList, args]
Lazy[NestList, f_, x_] := With[{y = f[x]}, MakeExprStructHold[{x, Splice[Lazy[NestList, f, y]]}]]

Lazy[Table][args___] := LazyExpression[#] & @ Lazy[Table, args]
Lazy[Table, expr_, {i_Symbol, from_, to_}] :=
    If[ from >= to,
        {},
        With[{elem = Block[{i = from}, expr], newFrom = from + 1},
            MakeExprStructHold[{elem, Splice[Lazy[Table, expr, {i, newFrom, to}]]}]
        ]
    ]
Lazy[Table, expr_, i_Symbol | {i_Symbol}] := Lazy[Table, expr, {i, 1, Infinity}]
Lazy[Table, expr_, {i_Symbol, to}] := Lazy[Table, expr, {i, 1, to}]


(* Properties *)

LazyExpressionProp[_, "Properties"] := {"Value", "HoldValue", "ExprStruct", "Get", "Set", "Eval", "Visualization", "Form"}

LazyExpressionProp[l_LazyExpression, First] := l["Part", 1]
LazyExpressionProp[l_LazyExpression, Rest] := l["Drop", 1]
LazyExpressionProp[l_LazyExpression, Head] := l["Part", 0]["Get"]
LazyExpressionProp[l_LazyExpression, ListQ] := l[Head] === List
LazyExpressionProp[l_LazyExpression, TreeQ] := l[Head] === Tree

LazyExpressionProp[Verbatim[LazyExpression][value_], "Value"] := value
LazyExpressionProp[Verbatim[LazyExpression][value_], "HoldValue"] := HoldComplete[value]

LazyExpressionProp[l_LazyExpression, "ExprStruct"] := l["Value"]["Get"]

LazyExpressionProp[l_LazyExpression, "Set", ds_] /; DataStructureQ[ds, "ExprStruct"] := (l["Value"]["Set", ds]; l)
LazyExpressionProp[l_LazyExpression, "Set", expr___] := l["Set", MakeExprStruct[Unevaluated[expr]]]
LazyExpressionProp[l_LazyExpression, "SetNoHead", expr___] := l["Set", MakeExprStruct[Unevaluated[expr]]["Part", 1]]

LazyExpressionProp[l_LazyExpression, "Get", head_ : HoldComplete] := l["ExprStruct"]["ConstructWith", head]["Get"]
LazyExpressionProp[l_LazyExpression, "ListGet"] /; l[ListQ] := With[{expr = Flatten[HoldComplete @@@ l["Get"]]},
	List @@@ HoldComplete[#] & @ Take[expr, First[FirstPosition[expr, elem_ /; !FreeQ[Unevaluated[elem], ref_Symbol /; LazyExpressionRefQ[Unevaluated[ref]]], {Length[expr]}, {1}, Heads -> False]]]
]

LazyExpressionEvaluate[expr_, holdRef_, m : _Integer | Infinity : 1, n : _Integer | Infinity : 1] := Block[{
    newExpr = expr
},
    (* Splice references verbatim *)
    newExpr = expr /. Verbatim[LazyExpression][ref_Symbol] /; LazyExpressionRefQ[Unevaluated[ref]] :> ref;
    (* Splice sub-references *)
    If[ m > 0,
        newExpr =
            With[{refPos = Position[newExpr, ref_Symbol /; LazyExpressionRefQ[Unevaluated[ref]]]},
            With[{refGroup = GroupBy[Thread[refPos :> Evaluate @ Extract[newExpr, refPos, Hold]], Last, Map[First]]},
            With[{refEval = Flatten[HoldComplete @@ Extract[
                    newExpr,
                    First /@ Values[refGroup],
                    Function[Null, LazyExpression[#]["Eval", m - 1, n]["Get"], HoldAll]
                ]]},
                ReplacePart[newExpr, List @@ Thread[
                    HoldComplete @@ Values[refGroup] :> refEval,
                    HoldComplete
                ]]
            ]]]
    ];
    (* Eval symbolically with blocked sub-references *)
    If[ n > 0,
        With[{refs = DeleteDuplicates @ Cases[newExpr, ref_Symbol /; LazyExpressionRefQ[Unevaluated[ref]] :> Hold[ref], All]},
            newExpr = Function[Null, Block[{$LazyUp = False}, Block[{##}, HoldComplete[##] &[ReleaseHold @ newExpr]]], HoldAll] @@ Flatten[Hold @@ refs]
        ]
    ];
    (* Splice Values (ideally there shouldn't be any) *)
    newExpr = newExpr /. ds_DataStructure /; DataStructureQ[ds, "Value"] :> RuleCondition[ds["Get"]];
    (* Splice ExprStructs *)
    With[{pos = Position[newExpr, ds_DataStructure /; DataStructureQ[ds, "ExprStruct"]]},
    With[{subExprs = Flatten[HoldComplete @@ Extract[newExpr, pos, #["ConstructWith", HoldComplete]["Get"] &], 1, HoldComplete]},
        newExpr = ReplacePart[newExpr, List @@ Thread[HoldComplete @@ pos :> subExprs, HoldComplete]]
    ]];
    (* Splice references verbatim *)
    newExpr = newExpr /. Verbatim[LazyExpression][ref_Symbol] /; LazyExpressionRefQ[Unevaluated[ref]] :> ref;

    (* Handle Sequence *)
    If[Length[newExpr] > 1, newExpr = Sequence @@@ HoldComplete[#] & @ newExpr];
    If[ n <= 0 || expr === newExpr,
        newExpr,
        LazyExpressionEvaluate[newExpr, holdRef, m, n - 1]
    ]
]

(* that's the only way I've found that triggers all Dynamics with the symbol *)
LazyExpressionProp[l_LazyExpression, "Trigger"] := Function[sym,
        Unprotect[sym];
        With[{tmp = sym}, sym =.; sym = tmp];
        (* Update[Unevaluated[sym]]; *)
        Protect[sym],
        HoldAllComplete
    ] @@ l["HoldValue"]

LazyExpressionProp[l_LazyExpression, "Eval",  m : _Integer | Infinity : 1, n : _Integer | Infinity : 1] := Block[{
    newExpr
},
    newExpr = LazyExpressionEvaluate[l["Get"], l["HoldValue"], m, n];
    l["Value"]["Set", MakeExprStruct[newExpr]["Part", 1]];
    l["Trigger"];
    l
]

LazyExpressionProp[l_LazyExpression, "ListEval", m : _Integer | Infinity : 1, n : _Integer | Infinity : 1] /; l[ListQ] := Block[{
    expr, restPos, restExpr, newRestExpr, newExpr
},
    expr = l["Get"];
    restPos = FirstPosition[expr, _ ? ValueQ, Missing["NoValue"], {2}, Heads -> False];
    If[ MissingQ[restPos],
        l,
        restExpr = Extract[expr, restPos, HoldComplete];
        While[True,
            newRestExpr = LazyExpressionEvaluate[restExpr, l["HoldValue"], m, n];
            If[ MatchQ[newRestExpr, HoldComplete[Splice[_]]],
                If[ MatchQ[newRestExpr, HoldComplete[Splice[_List]]],
                    newRestExpr = FlattenAt[newRestExpr, {{1}, {1, 1}}]
                ];
                Break[]
            ];
            If[newRestExpr === restExpr, Break[]];
            restExpr = newRestExpr;
            Break[]
        ];
        newExpr = FlattenAt[ReplacePart[expr, restPos :> # & @ newRestExpr], restPos];
        l["Value"]["Set", MakeExprStruct[newExpr]["Part", 1]];
        l["Trigger"];
        l
    ]
]

LazyExpressionProp[l_LazyExpression, "DynamicGet", lvl_ : 1] := Block[{expr = l["Get"], pos},
	pos = ReverseSortBy[Position[expr, _ ? ValueQ, {2, Infinity}], Length, LexicographicOrder];
	Fold[With[{
        holdRef = l["HoldValue"], p = #2[[1]], subExpr = #2[[2]]
    },
    With[{
        eval = If[Length[#] > 0, #[[1, 1, 1, 1]], subExpr] & [Function[Null, MultiEvaluate[Unevaluated[#], {{}}], HoldAllComplete] @@ subExpr]
    },
        ReplacePart[
            #1,
            p -> Replace[subExpr, {
                holdSubRef : HoldComplete[subRef_Symbol] /; LazyExpressionRefQ[Unevaluated[subRef]] :>
                    If[ holdSubRef === holdRef,
                        Tooltip["🔄", SymbolName[Unevaluated[subRef]]],
                        If[lvl > 0, LazyExpression[subRef]["Visualization", lvl], SymbolName[Unevaluated[subRef]]]
                    ],
                _ :> Framed[
                    EventHandler[
                        Tooltip[
                            Style[HoldForm @@ First[Extract[#1, {p}, HoldComplete]], Black],
                            Function[Null, Column[{
                                HoldForm[#],
                                "\[DownArrow]",
                                If[ MatchQ[eval, _HoldForm],
                                    ContextFreeHoldForm @@ eval,
                                    "Kernel"
                                ]
                            },
                                Alignment -> Center
                            ], HoldAll] @@ subExpr
                        ],
                        {"MouseClicked" :> (
                            l["SetNoHead", ReplacePart[l["Get"], Function[Null, p :> ##, HoldAllComplete] @@
                                LazyExpressionEvaluate[eval, l["HoldValue"], If[CurrentValue["OptionKey"], 1, 0], If[CurrentValue["OptionKey"], 0, 1]]]];
                            l["Trigger"]
                        )},
                        PassEventsUp -> False
                    ],
                    FrameStyle -> {Black, Dashed}
                ]
            }]
        ]
    ]] &,
        Replace[expr, HoldComplete[Sequence[seq___]] :> HoldComplete[HoldForm[Sequence][seq]]],
        Thread[{pos, Extract[expr, pos, HoldComplete]}]
    ]
]

LazyExpressionProp[l_LazyExpression, "Visualization", lvl_ : 1] :=
    Function[
        ref,
        DynamicModule[{button},
            button = EventHandler[
                Tooltip[
                    Dynamic[
                        Module[{show},
                            Unprotect[ref];
                            show =Framed[
                                HoldForm @@ LazyExpression[ref]["DynamicGet", lvl - 1],
                                RoundingRadius -> 5
                            ];
                            Protect[ref];
                            show
                        ],
                        TrackedSymbols :> {ref}
                    ],
                    Column[{"LazyExpression"[SymbolName[Unevaluated[ref]]], LazyExpression[ref]["Form"]}, Alignment -> Center]
                ],
                "MouseClicked" :> (LazyExpression[ref][If[l[ListQ], "ListEval", "Eval"], If[CurrentValue["OptionKey"], 1, If[CurrentValue["CommandKey"], 1, 0]], If[CurrentValue["OptionKey"], 0, 1]]; button = None),
                PassEventsUp -> False
            ];
            Dynamic[
                Replace[button, None :> RawBoxes[MakeBoxes[LazyExpression[ref]]]],
                TrackedSymbols :> {button}
            ]
        ],
        HoldAll
    ] @@ l["HoldValue"]

LazyExpressionProp[l_LazyExpression, "Form"] := HoldForm @@ DisableFormatting /@ ReplaceAll[l["Get"], sym_Symbol :> SymbolName[Unevaluated[sym]]]
LazyExpressionProp[l_LazyExpression, args___] := l["ExprStruct"][args]

LazyExpressionProp[l_LazyExpression, "Graph", opts___] := Block[{
	expr,
	sources = {HoldForm @@ l["HoldValue"]},
	source,
	targets,
	vertices = {},
	edges = {}
},
	While[Length[sources] > 0,
		source = First[sources];
		expr = (LazyExpression @@ source)["Get"];
		targets = Cases[expr, ref_Symbol /; LazyExpressionRefQ[Unevaluated[ref]] :> HoldForm[ref], All];
		If[MemberQ[targets, source], targets = DeleteCases[targets, source]; AppendTo[edges, DirectedEdge[source, source, source]]];
		If[ targets === {},
			With[{evalExpr = (LazyExpression @@ source)["Eval", 0, 1]["Get"]},
				If[evalExpr === expr, sources = Rest[sources]; AppendTo[vertices, source]]
			],
			sources = Rest[sources];
			AppendTo[vertices, source]
		];
		edges = Join[edges, DirectedEdge[source, #, #] & /@ targets];
		sources = DeleteElements[Join[sources, targets], vertices];
	];
	Graph[vertices, edges,
        opts,
		VertexShapeFunction -> Function @ Inset[
			Replace[#2, HoldForm[ref_Symbol] :>
				(* Tooltip[
					Framed[
						Style[
							HoldForm @@ LazyExpression[ref]["Get"] /. subRef_Symbol /; LazyExpressionRefQ[Unevaluated[subRef]] :>
                                RuleCondition[With[{
                                    name = SymbolName[Unevaluated[subRef]],
                                    subExpr = HoldForm @@ LazyExpression[subRef]["Get"] /. sym_Symbol :> RuleCondition[If[MemberQ[$ContextPath, Context[sym]] && !ValueQ[sym], sym, SymbolName[Unevaluated[sym]]]]
                                },
                                    Tooltip[ClickToCopy[name, Interpretation[subExpr, LazyExpression[subRef]]], subExpr]]
                                ],
							Black
						],
						FrameStyle -> Black
					],
					SymbolName[Unevaluated[ref]]
				] *)
                Style[LazyExpression[ref]["Visualization", 0], Black]
			],
			#1,
			#3
		],
		EdgeLabels -> DirectedEdge[_, _, HoldForm[ref_Symbol]] :>
            With[{name = SymbolName[Unevaluated[ref]]}, Framed[ClickToCopy[name, Interpretation[HoldForm[DisableFormatting[LazyExpression[ref]]], LazyExpression[ref]]], FrameStyle -> None, Background -> White]],
		PerformanceGoal -> "Quality"
	]
]

SetAttributes[LazyExpressionProp, HoldFirst]


lazy_LazyExpression[args___] /; LazyExpressionQ[Unevaluated[lazy]] :=
    Function[Null, LazyExpressionProp[lazy, ##], HoldAllComplete] @@ Unevaluated /@ HoldComplete[args]


(* Q *)

LazyExpressionRefQ[ref_Symbol] :=
    MemberQ[$LazyExpressionSymbols, Hold[ref]] && System`Private`HoldValidQ[ref] && ! LazyExpressionQ[ref] && DataStructureQ[ref, "Value"] && DataStructureQ[ref["Get"], "ExprStruct"]
LazyExpressionRefQ[___] := False

LazyExpressionQ[lazy : Verbatim[LazyExpression][ref_Symbol]] := LazyExpressionRefQ[Unevaluated[ref]]
LazyExpressionQ[___] := False


(* Construction *)

LazyExpression[ds_DataStructure, name: _Symbol : Automatic] /; DataStructureQ[ds, "ExprStruct"] :=
    With[{ref = Replace[name, {Automatic -> Block[{$ModuleNumber = 1}, Unique["ref$"]]}]},
        If[ ! LazyExpressionRefQ[ref],
            ref = CreateDataStructure["Value", ds];
            System`Private`HoldSetValid[ref];
            SetAttributes[ref, {Protected, Temporary}];
            AppendTo[$LazyExpressionSymbols, Hold[ref]]
        ];
        LazyExpression[ref]
    ]

lazy : LazyExpression[expr_, name : _Symbol : Automatic] /; ! LazyExpressionQ[Unevaluated[lazy]] :=
    Function[Null, If[$LazyExpressionCache, If[name === Automatic, LazyExpression[expr] = #, LazyExpression[expr, name] = #], #], HoldAll] @
        With[{ds = MakeExprStruct[Unevaluated[expr]]}, LazyExpression[ds, name]]

LazyExpression /: l_LazyExpression /; $LazyNoEntry && System`Private`HoldEntryQ[l] := System`Private`HoldSetNoEntry[l]


(* Formatting *)


LazyExpression /: MakeBoxes[lazy_LazyExpression /; LazyExpressionQ[Unevaluated[lazy]], ___] := With[{
    boxes = ToBoxes[lazy["Visualization", 2]]
},
    InterpretationBox[boxes, lazy]
]


(* UpValues *)

LazyExpression::undef = "is not defined for ``"

LazyExpression /: f_Symbol[left___, l_LazyExpression, right___] /; MemberQ[Attributes[f], Listable] && LazyExpressionQ[Unevaluated[l]] && l[ListQ] := Lazy[Map][f[left, #, right] &, l]
LazyExpression /: f_Symbol[ls___LazyExpression] /; MemberQ[Attributes[f], Listable] && AllTrue[Unevaluated[{ls}], Function[Null, LazyExpressionQ[Unevaluated[#]] && #[ListQ], HoldAll]] := Lazy[MapThread][f, {ls}]

LazyExpression /: expr : (f : Except[LazyExpressionRefQ | LazyExpressionQ | LazyExpressionProp])[left___, lazy_LazyExpression /; LazyExpressionQ[Unevaluated[lazy]], right___] /; $LazyUp && ! SequenceHoldQ[Unevaluated[expr]] := With[{
    i = Length[HoldComplete[left]] + 1, holdExpr = HoldComplete[expr]
},
    With[{pos = Position[holdExpr, l_LazyExpression /; LazyExpressionQ[Unevaluated[l]]]},
    With[{refs = Flatten[HoldComplete @@ Extract[holdExpr, pos, Function[Null, #["HoldValue"], HoldAll]]]},
        LazyExpression @@ ReplacePart[holdExpr, List @@ Thread[HoldComplete @@ pos :> refs, HoldComplete]]
    ]] /; ! HoldPositionQ[Unevaluated[expr], i]
]

LazyExpression[_, __] := $Failed

SetAttributes[LazyExpression, HoldAllComplete]

