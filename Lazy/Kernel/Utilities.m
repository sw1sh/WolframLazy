Package["Wolfram`Lazy`"]


PackageExport["ApplyUnevaluated"]



ApplyUnevaluated[expr_, then_, else_ : Identity] := With[{eval = expr}, If[eval === Unevaluated[expr], then[eval], else[eval]]]

SetAttributes[ApplyUnevaluated, HoldAll]

