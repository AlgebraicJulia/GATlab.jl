using GATlab, GATlab.Stdlib, .ThCategory

# (@macroexpand1 ThCategory.Meta.@wrapper Foo Any) |> Base.remove_linenums!
c = CatWrapper(FinSetC());
c′ = Foo(FinSetC())

A = [2, 1]

cmp = compose[getvalue(c)]
@time foldl((x,y)->compose(c, x,y), fill(A, 600001));
@time foldl(cmp, fill(A, 600001));

VSCodeServer.@profview foldl((x,y)->compose(c, x,y), fill(A, 600001));
VSCodeServer.@profview foldl(cmp, fill(A, 600001));

# Typed wrappers
################
# (@macroexpand1 ThCategory.Meta.@typed_wrapper Foo Any) |> Base.remove_linenums!)

ThCategory.Meta.@typed_wrapper Foo

cmp = compose[getvalue(c′)]
@time foldl((x,y)->compose(c′, x,y), fill(A, 600001));
@time foldl(cmp, fill(A, 600001));
