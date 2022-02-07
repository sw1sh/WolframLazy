Package["Lazy`"]

PackageScope["MapAtInplace"]



MapAtInplace[f_, expr_, pos_] := ReplacePart[expr, Extract[expr, pos, f], pos]
MapAtInplace[f_, pos_][expr_] := MapAtInplace[f, expr, pos]

