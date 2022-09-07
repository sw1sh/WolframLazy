Package["Wolfram`Lazy`"]


PackageExport["Nat"]
PackageExport["FromNat"]



SetAttributes[Nat, HoldFirst]


Nat[n : _Integer : 0] := Nat[0, n]
Nat[Infinity] := Nat[Nat[Infinity], 1]
Nat[x_] := Nat[x, 0]
Nat[Nat[x_, n_], m_ : 1] := Nat[x, n + m]
Nat[LazyValue[x_], m_ : 1] := Nat[x, m]


FromNat[Nat[x_Integer, n_]] := n + x
FromNat[Nat[x_, n_]] := n + LazyValue[FromNat[x]]
FromNat[n_Integer] := n
FromNat[LazyValue[x_]] := FromNat[x]
FromNat[___] := $Failed

x_ < n : Nat[_, z_] ^:= x < z || x < FromNat[n]
x_ <= n : Nat[_, z_] ^:= x <= z || x <= FromNat[n]

n : Nat[_, x_] > z_ ^:= x > z || FromNat[n] < z
n : Nat[_, x_] >= z_ ^:= x >= z || FromNat[n] <= z

Nat /: n : Nat[_, x_] <= Infinity := True
Nat /: n : Nat[_, x_] > Infinity := False
Nat /: Infinity < n : Nat[_, x_] := False
Nat /: Infinity >= n : Nat[_, x_] := True


Normal[n_Nat] ^:= FromNat[n]

Format[nat_Nat] ^:= Interpretation[Tooltip["Nat"[FromNat[nat]], InputForm[nat]], nat]

