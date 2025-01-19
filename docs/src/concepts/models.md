# Models and instances

A *model* is any julia value `m` that satisfies `m :: Model`. A model may *implement* one or more theories; to check if a model `m` is implements a theory `Th`, one can run `implements(m, Th)::Bool`, to check if `m` implements all operations in `Th`.

When a model `m` implements `Th`, the following methods should be defined.

1. For every type constructor `X` in `Th`

   ```julia
   Th.X[m::typeof(m)](x, args...) = ...
   ```
   
   This attempts to coerce `x` into a valid element of the type constructor `X` applied to args `args...`, and throws an error if this is not possible.
   
   For instance, `ThCategory.Hom[FinSetC()](xs::Vector{Int}, dom::Int, codom::Int)` returns `xs` if and only if `length(xs) == dom` and `all(1 .<= xs .<= codom)`, and otherwise errors.
   
   This is syntactic sugar (via an overload of `Base.getindex(::typeof(ThCategory.Hom), ::Model)`) for calling `ThCategory.Hom(TheoryInterface.WithModel(FinSetC()), xs, dom, codom)`. The reason that we do not simply have `ThCategory.Hom(FinSetC(), xs, dom, codom)` is a long story; essentially it has to do with maintaining compatibility with Catlab. But one advantage of this is that you can define `Hom = ThCategory.Hom[FinSetC()]`, and then use that locally.

2. For each argument `a` to a type constructor (i.e. `dom` and `codom` for `Hom`), an overload of

   ```julia
   Th.a[m::typeof(m)](x) = ...
   ```

   This opportunistically attempts to retrieve the type argument for x. For instance, `ThCategory.dom[FinSetC()]([1,2,3]) = 3`. However, this *may* return an error, as for instance `ThCategory.codom[FinSetC()]([1,2,3])` is uncertain; it could be a morphism into any `n >= 3`. This is because morphisms don't have to know their domain and codomain.

3. For each term constructor `f` in `Theory`

   ```julia
   Th.f[m::typeof(m)](args...) = ...
   ```
    
   This applies the term constructor to arguments that are assumed to be a valid type (i.e., they have previously been coerced by the type constructors). For instance,

   ```julia
   ThCategory.compose[FinSetC()]([1,3,2], [1,3,2]) == [1,2,3]
   ```

   Term constructors sometimes need to know the values of elements of their context that are not arguments. For instance, `compose(f::Hom(A,B), g::Hom(B,C))` might need access to the values of `A`, `B` or `C`, which might not be able to be inferred from `f` and `g`. In this case, we support passing a named tuple called `context` to provide these additional values, named with their variables names in the theory. So for instance, we would allow `ThCategory.compose[FinSetC()]([1,3,2], [1,3,2]; (;B=3))`. It is rare that this is needed, however.


In order to make a model implement a theory, one can either manually implement all of the methods, or use the `@instance` macro. You can see examples of using the `@instance` macro in [`src/stdlib/models`](https://github.com/AlgebraicJulia/GATlab.jl/tree/main/src/stdlib/models).