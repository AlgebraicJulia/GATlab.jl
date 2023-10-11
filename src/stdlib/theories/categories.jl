export ThClass, ThGraph, ThLawlessCat, ThAscCat, ThCategory, ThThinCategory

import AlgebraicInterfaces: dom, codom, compose, id, Ob, Hom


# Category theory
#################

"""    ThClass

A Class is just a Set that doesn't worry about foundations.

"""
@theory ThClass begin
  Ob::TYPE ⊣ []
end

"""    ThGraph

A graph where the edges are typed depending on dom/codom. Contains all
necessary types for the theory of categories.
"""
@theory ThGraph <: ThClass begin
  @op (→) := Hom
  Hom(dom::Ob, codom::Ob)::TYPE
end

"""    ThLawlessCat

The data of a category without any axioms of associativity or identities.
"""
@theory ThLawlessCat <: ThGraph begin
  @op (⋅) := compose
  compose(f::(a → b), g::(b → c))::(a → c) ⊣ [(a,b,c)::Ob]
end


"""    ThAsCat

The theory of a category with the associative law for composition.
"""
@theory ThAscCat <: ThLawlessCat begin
  assoc := ((f ⋅ g) ⋅ h) == (f ⋅ (g ⋅ h)) ⊣
    [(a, b, c, d)::Ob, f::(a→b), g::(b→c), h::(c→d)]
end

"""    ThIdLawlessCat

The theory of a category without identity axioms.
"""
@theory ThIdLawlessCat <: ThAscCat begin
  id(a::Ob)::Hom(a,a)
end

"""    ThCategory

The theory of a category with composition operations and associativity and identity axioms.
"""
@theory ThCategory <: ThIdLawlessCat begin
  idl := id(a) ⋅ f == f ⊣ [a::Ob, b::Ob, f::Hom(a,b)]
  idr := f ⋅ id(b) == f ⊣ [a::Ob, b::Ob, f::Hom(a,b)]
end

"""    ThThinCategory

The theory of a thin category meaning that if two morphisms have the same domain and codomain they are equal as morphisms.
These are equivalent to preorders.
"""
@theory ThThinCategory <: ThCategory begin
  thineq := f == g ⊣ [a::Ob, b::Ob, f::Hom(a,b), g::Hom(a,b)]
end
