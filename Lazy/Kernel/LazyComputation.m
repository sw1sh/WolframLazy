Package["Wolfram`Lazy`"]

PackageExport["LazyComputation"]



LazyComputationDataQ[data_Association] := MatchQ[Unevaluated[data],
    KeyValuePattern[{
        "Lazy" -> _,
        Method -> _String,
        "Options" -> OptionsPattern[]
    }]
]

LazyComputationDataQ[___] := False


LazyComputation[data_Association][prop_String] /; KeyExistsQ[data, prop] := data[prop]

LazyComputation[data_Association]["Properties"] := Sort[Join[Keys[data], {"Continue"}]]

LazyComputation[data_Association]["Association"] := data

LazyComputation[data_Association]["Dataset"] := Dataset[data]

LazyComputation[data_Association]["Continue", opts : OptionsPattern[]] := Switch[data[Method],
    "FindPath",
    With[{newData = LazyFindPath[
            data["Lazy"],
            data["Target"],
            data["Position"],
            data["Visited"],
            FilterRules[{opts}, Options[LazyFindPath]],
            data["Options"]
        ]["Association"]
    },
        LazyComputation[<|
            data,
            "Lazy" -> newData["Lazy"],
            "Position" -> newData["Position"],
            "Visited" -> newData["Visited"],
            "Paths" -> Join[data["Paths"], newData["Paths"]],
            "Options" -> DeleteDuplicatesBy[Join[{opts}, data["Options"]], First]
        |>]
    ],
    _,
    $Failed
]

MakeBoxes[LazyComputation[data_Association /; LazyComputationDataQ[Unevaluated[data]]], format_] ^:= With[{
    icon = Framed["\[Ellipsis]"]
},
    BoxForm`ArrangeSummaryBox[
        "LazyComputation",
        l,
        icon,
        {{BoxForm`SummaryItem[{"Method: ", data[Method]}]}},
        {
            Switch[data[Method],
                "FindPath", {
                    BoxForm`SummaryItem[{"Target: ", data["Target"]}],
                    BoxForm`SummaryItem[{"Paths: ", data["Paths"]}]
                },
                _,
                {}
            ],
            {BoxForm`SummaryItem[{"Options: ", Row[data["Options"], ","]}]}
        },
        format
    ]
]

