# Compute Graphs

A compute graph is, essentially, a morphism in a free Markov category. That is, it is a string diagram where wires can be arbitrarily split/discarded. However, it does not necessarily have a fixed domain/codomain.

It is a free Markov category not necessarily because it has anything to do with probability, but just because

```julia
x1 = f(y)
x2 = f(y)
```

has a different representation than

```julia
x1 = f(y)
x2 = x1
```

That is, a compute graph is not necessarily _deduplicated_.

Given any GAT, we can produce a model family of structs that contain compute graphs. The types of elements for this model family are `TypedVar{T}`s, where `T` is a type parameter that takes values in the type functions in the theory (e.g. `ThCategory.Ob`, `ThCategory.Hom`). However, `T` does not appear in the fields for `TypedVar`; it is only there to guide dispatch. The implementation of methods for these models adds a new node to the compute graph with the desired term constructor, and then returns a `TypedVar` containing the `Id` of the new node.

If we add a hashcons to a compute graph, we are essentially deduplicating terms. A hashconsed compute graph is essentially a morphism in a free Cartesian category, and

```julia
x1 = f(y)
x2 = f(y)
```

and

```julia
x1 = f(y)
x2 = x1
```

will produce the same result.

Finally, if we upgrade from compute graph to e-graph, we essentially are equipping every object in the category with a monoid structure dual to the comonoid structure. That is, we have the ability to "join" wires to force them to be equal.

I think this might turn out to be something like "relations for the free regular completion of the cartesian category."
