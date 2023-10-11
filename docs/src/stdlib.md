# Standard Library

## Categories

Our friend `ThCategory` is the main theory in this module.

```@docs
GATlab.Stdlib.StdTheories.ThCategory
```

You can specialize a theory by adding more axioms. In this case we can specialize the theory of categories to that of thin category by adding the axiom that two morphisms are equal if they have the same domain and codomain.

```
thineq := f == g :: Hom(A,B) ⊣ [A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B)]
```

```@docs
GATlab.Stdlib.StdTheories.ThThinCategory
```
### Category Building Blocks
The remaining theories in this module are not necessarily useful, but go to show demonstrate the theory hierarchy can be built up in small increments.

```@docs
GATlab.Stdlib.StdTheories.ThClass
```

```@docs
GATlab.Stdlib.StdTheories.ThLawlessCat
```

```@docs
GATlab.Stdlib.StdTheories.ThAscCat
```

```@docs
GATlab.Stdlib.StdTheories.ThIdLawlessCat
```

```@autodocs
Modules = [GATlab.Stdlib,
  GATlab.Stdlib.StdTheories,
  GATlab.Stdlib.StdModels,
  ]
```
