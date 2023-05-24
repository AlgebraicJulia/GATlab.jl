# For Catlab users

Gatlab is a refactoring of the core GAT system in Catlab. There are three main differences between the Gatlab GAT system and the Catlab GAT system, in addition to a variety of new features enabled by these differences.

## 1. Models as values

Instances (or models) of GATs in Catlab worked on a system analogous to Haskell type classes. That is, given a type and a GAT, that type could be involved in at most one instance of the GAT. However, there are many, many categories that have, for instance, integers as objects. The way to fix this was to make lots of "newtype" wrappers, like

```julia
struct FinSetInt
  n::Int
end
```

This is not ideal, but the larger problem is that this made it difficult to have models of a GAT that were parameterized by other models, because there was no way of referring to a particular model. So constructions like slice categories, dual categories, or cospan categories were not easy to do.

In Gatlab, we instead do models of GATs in a more "Standard ML" style. That is, each model is a *value* that can be passed around dynamically. Then the implementations of the GAT term constructors are attached via multiple dispatch to that value. In simple cases, that value might be the unique instance of a zero-field struct, but more generally there could be more data inside the value, as is the case for slice categories. If the struct has fields, then we can think of it like a "functor" in ML parlance (which has little to do with the standard categorical use of the word functor); i.e. it is a parameterized model of the theory.

Sometimes we refer to this by "categories as contexts", because the category (i.e., the model of the theory of categories) serves as a context for disambiguating which method to use, and this is a pun off of the famous category theory book "Categories in Context" by Emily Riehl.

## 2. E-Graphs

An e-graph is a data structure used to store congruence relations on a collections of terms. A congruence relation is an equivalence relation with the property that if $x_{i} \sim x_{i}'$, then $f(x_{1},\ldots,x_{n}) \sim f(x_{1}',\ldots,x_{n}')$ for any term constructor $f$. E-graphs are used for a variety of purposes, including:

- finding simple representations of terms
- deciding whether two terms are equal

The syntax systems we use for GATs in Gatlab are built from the ground-up to be compatible with a purpose-built e-graph implementation. This allows us to make use of the axioms in a GAT to rewrite terms and perform equational reasoning.

Additionally, it allows us to perform a weak form of typechecking. Typechecking in general for a GAT requires deciding the equality of arbitrary terms, which is undecidable. However, we can typecheck "up to" the collection of equivalences that we have recorded in an e-graph. Any well-typed term can be typechecked using this procedure by first placing the necessary equalities in the e-graph and then running the type-checking algorithm. Moreover, whenever this algorithm finds a positive result, one can be sure that the term does in fact typecheck. This is analogous to the termination-checking in proof assistants; we circumvent undecidability by putting the burden on the user to give us some additional data to show that their program is valid. And in many circumstances, very little additional data is required. For instance, in the bare theory of categories, there are no term constructors that produce objects. So checking whether two objects are equal in a presentation of a category is a simple problem of computing an equivalence relation (instead of a congruence relation). Thus, typechecking is very easy in this circumstance.

## 3. Indexed dependent types in models

A morphism between the finite sets $\{1,\ldots,n\}$ and $\{1,\ldots,m\}$ is simply a length-$n$ vector whose entries are in $\{1,\ldots,m\}$. However, in Catlab we cannot make a model of the theory of categories which has `Vector{Int}` as its type for morphisms. This is because we require an implementation of `dom` and `codom` to have a model, and it is not possible to infer the size of the codomain from a `Vector{Int}`.

Mathematically, this can be interpreted as a requirement that models of GATs interpret the dependent types as *fibered*. I.e. the dependent type `Hom(a::Ob,b::Ob)` gets interpreted as a Julia type `Hom` with functions `dom, codom` from `Hom` to `Ob`.

The practical downside to this is that if you want to store several morphisms that have the same domain/codomain, you have to redundantly store the domain and codomain. So although a C-set consists of a collection of objects and morphisms in `FinSet`, we do not actually define it in this way in Catlab, because we don't want to redundantly store the objects in each morphism.

In Gatlab, we fix this in the following way. When you declares a model in Gatlab, you associate types to it that correspond to the "bare" data. I.e., we would just associate `Vector{Int}` to `Hom` in an implementation of `FinSet`. Then various methods expect you to pass in the domain and codomain of a morphism in addition to the data of the morphism, rather than assuming that you can infer the domain and codomain from the data.

Mathematically, we interpret this by saying that we interpret the dependent types as *indexed*. That is, we assign a set to each pair of objects, *and those sets can intersect*. I.e., `Hom(a,b)` could intersect non-trivially `Hom(c,d)`. So whenever we handle a morphism, we need external data that tells us what the domain and codomain is.

Notice that from such an implementation, we can automatically derive a wrapper type which contains domain, codomain, and data. But we can't go the other way; we can't automatically "pick out" what is data and what is just recording domain/codomain from the fibered implementation.

Although mathematically, fibered and indexed dependent types are equivalent, they have different implementations, and we hope that the indexed point of view will end up being more natural for our purposes.
