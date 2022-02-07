Package["Lazy`"]

PackageExport["Lazy"]



Lazy[{}] := Cons[]
Lazy[{x_, rest___}] := Cons[x, Lazy[{rest}]]

