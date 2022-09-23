Package["Wolfram`Lazy`"]

PackageScope["ApplyUnevaluated"]
PackageScope["HoldAtom"]
PackageExport["HoldPosition"]
PackageExport["HoldPositionQ"]
PackageExport["SequenceHoldQ"]
PackageExport["ContextFreeForm"]
PackageExport["ContextFreeHoldForm"]



ApplyUnevaluated[expr_, then_, else_ : Identity] := With[{eval = expr}, If[eval === Unevaluated[expr], then[eval], else[eval]]]

SetAttributes[ApplyUnevaluated, HoldAll]


HoldAtom[atom_] := Block[{link = LinkCreate[LinkMode -> Loopback], holdExpr},
	LinkWrite[link, Hold[atom]];
	holdExpr = LinkRead[link];
	LinkClose[link];
	holdExpr
]

HoldPositionFromAttributes[attrs_, len_] :=
    Which[
        MemberQ[attrs, HoldAll | HoldAllComplete] || ContainsAll[attrs, {HoldFirst, HoldRest}],
        Range @ len,
        MemberQ[attrs, HoldFirst],
        {1},
        MemberQ[attrs, HoldRest],
        Range[2, len],
        True,
        {}
    ]

HoldPosition[sym_Symbol[args___]] := HoldPositionFromAttributes[Attributes[sym], Length[HoldComplete[args]]]
HoldPosition[Verbatim[Function][_, _, attrs___][args___]] := HoldPositionFromAttributes[Flatten[{attrs}], Length[HoldComplete[args]]]
HoldPosition[_[___]] := {}
HoldPosition[___] := Missing["Position"]

HoldPositionQ[expr_, i_] := With[{pos = HoldPosition[Unevaluated[expr]]}, MissingQ[pos] || MemberQ[pos, i]]

SequenceHoldQ[sym_Symbol[___]] := MemberQ[Attributes[sym], SequenceHold]
SequenceHoldQ[_] := False


(* carefully replace symbols with context with symbols without context *)
ContextFreeForm[expr_, form_ : InputForm] := With[{pos = Position[form[expr], sym_Symbol /; !MemberQ[$ContextPath, Context[sym]]]},
    With[{holdSymbols = Flatten[Hold @@ Extract[form[expr], pos, Function[Null, ToExpression[SymbolName[Unevaluated[#]], InputForm, Hold], HoldAll]]]},
       ReplacePart[form[expr], List @@ Thread[Hold @@ pos :> holdSymbols, Hold]]
    ]
]

ContextFreeHoldForm[expr_, form_ : InputForm] := ContextFreeForm[Unevaluated[form[expr]], HoldForm]
SetAttributes[ContextFreeHoldForm, HoldAll]
