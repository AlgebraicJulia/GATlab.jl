# Symbolic Models

Theories can also be instantiated as systems of symbolic expressions, using the
[`@symbolic_model`](@ref) macro. The symbolic expressions are expression trees,
as commonly used in computer algebra systems. They are similar to Julia's `Expr`
type but they are instead subtyped from GATlab's [`GATExpr`](@ref) type and they
have a more refined type hierarchy.

A single theory can have different syntax systems, treating different terms
as primitive or performing different simplication or normalization procedures.
GATlab tries to make it easy to define new syntax systems. Many of the
theories included with GATlab have default syntax systems, but the user is
encouraged to define their own to suit their needs.

To get started, you can always call the `@symbolic_model` macro with an empty body.
Below, we subtype from GATlab's abstract types `ObExpr` and `HomExpr` to enable
LaTeX pretty-printing and other convenient features, but this is not required.

```@example category
@symbolic_model CategoryExprs{ObExpr, HomExpr} ThCategory begin
end
A, B, C, D = [ Ob(CategoryExprs.Ob, X) for X in [:A, :B, :C, :D] ]
f, g, h = Hom(:f, A, B), Hom(:g, B, C), Hom(:h, C, D)
compose(compose(f,g),h)
```

The resulting symbolic expressions perform no simplification. For example, the
associativity law is not satisfied:

```@example category
compose(compose(f,g),h) == compose(f,compose(g,h))
```

Thus, unlike instances of a theory, syntactic expressions are not expected to
obey all the axioms of the theory.

However, the user may supply logic in the body of the `@symbolic_model` macro to enforce
the axioms or perform other kinds of simplification. Below, we use the
[`associate`](@ref) function provided by GATlab to convert the binary
expressions representing composition into $n$-ary expressions for any number
$n$. The option `strict=true` tells GATlab to check that the domain and codomain
objects are strictly equal and throw an error if they are not.

```@example category
@symbolic_model SimplifyingCategoryExprs{ObExpr, HomExpr} ThCategory begin
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end
A, B, C, D = [ Ob(SimplifyingCategoryExprs.Ob, X) for X in [:A, :B, :C, :D] ]
f, g, h = Hom(:f, A, B), Hom(:g, B, C), Hom(:h, C, D)
compose(compose(f,g),h)
```

Now the associativity law *is* satisfied:

```@example category
compose(compose(f,g),h) == compose(f,compose(g,h))
```

### Primitive versus derived operations

In some algebraic structures, there is a choice as to which operations should be
considered primitive and which should be derived. For example, in a [cartesian
monoidal category](https://ncatlab.org/nlab/show/cartesian+monoidal+category),
the copy operation $\Delta_X: X \to X \otimes X$ can be defined in terms of the
pairing operation $\langle f, g \rangle$, or vice versa. In addition, the
projections $\pi_{X,Y}: X \otimes Y \to X$ and $\pi_{X,Y}': X \otimes Y \to Y$
can be defined in terms of the deleting operation (terminal morphism) or left as
primitive.

In GATlab, the recommended way to deal with such situations is to define *all*
the operations in the theory and then allow particular syntax systems to
determine which operations, if any, will be derived from others. In the case of
the cartesian monoidal category, we could define a signature `CartesianCategory`
by inheriting from the builtin theory `SymmetricMonoidalCategory`.

```@setup cartesian-monoidal-category
using GATlab
```

```@example cartesian-monoidal-category
@signature ThCartesianCategory <: ThSymmetricMonoidalCategory begin
  mcopy(A::Ob)::(A → (A ⊗ A))
  delete(A::Ob)::(A → munit())
  pair(f::(A → B), g::(A → C))::(A → (B ⊗ C)) ⊣ (A::Ob, B::Ob, C::Ob)
  proj1(A::Ob, B::Ob)::((A ⊗ B) → A)
  proj2(A::Ob, B::Ob)::((A ⊗ B) → B)
end
nothing # hide
```

We could then define the copying operation in terms of the pairing.

```@example cartesian-monoidal-category
@symbolic_model CartesianCategoryExprsV1{ObExpr,HomExpr} ThCartesianCategory begin
  mcopy(A::Ob) = pair(id(A), id(A))
end
A = Ob(CartesianCategoryExprsV1.Ob, :A)
mcopy(A)
```

Alternatively, we could define the pairing and projections in terms of the
copying and deleting operations.

```@example cartesian-monoidal-category
@symbolic_model CartesianCategoryExprsV2{ObExpr,HomExpr} ThCartesianCategory begin
  pair(f::Hom, g::Hom) = compose(mcopy(dom(f)), otimes(f,g))
  proj1(A::Ob, B::Ob) = otimes(id(A), delete(B))
  proj2(A::Ob, B::Ob) = otimes(delete(A), id(B))
end
A, B, C = [ Ob(CartesianCategoryExprsV2.Ob, X) for X in [:A, :B, :C] ]
f, g = Hom(:f, A, B), Hom(:g, A, C)
pair(f, g)
```
