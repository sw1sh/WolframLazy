Package["Lazy`"]

PackageExport["LazyTree"]
PackageExport["LazyTreeForm"]
PackageExport["ConsTree"]



SetAttributes[LazyTree, HoldAll]

ToTree[LazyTree[data_, children_Cons]] ^:=  Tree[data, Map[ToTree, Normal@children]]
ToTree[x_] := x

Normal[t_LazyTree] ^:= ToTree[t]

TreeData[LazyTree[data_, _]] ^:= data
TreeChildren[LazyTree[_, children_Cons]] ^:= children

LazyTree /: TreeExtract[t_LazyTree, Cons[]] := t
Cons /: TreeExtract[t_, Cons[]] := t
LazyTree /: TreeExtract[t_LazyTree, Cons[p_, s_]] := TreeExtract[TreeChildren[t][[p]], s]
TreeExtract[t_, _Cons] ^:= t


LazyTreeForm[LazyTree[data_, Cons[]]] := Tree[data]
LazyTreeForm[LazyTree[data_, Cons[x_, l_Cons]]] := Tree[data, {
    LazyTreeForm @ x,
    Splice @ LazyListForm @ Map[Function[y, LazyTreeForm[Unevaluated @ y], HoldFirst], l]
}]
LazyTreeForm[x_] := Shallow[x, {2, 2}]


ConsTree[Cons[x_, l_]] := LazyTree[Cons, Cons[x, Cons[ConsTree[l], Cons[]]]]
ConsTree[Cons[]] := LazyTree[Cons]
ConsTree[x_] := x

