module Categories
export ThClass, ThGraph, ThLawlessCat, ThAscCat, ThCategory, ThThinCategory

using ....Syntax

# Category theory
@theory ThClass begin
  Ob::TYPE ⊣ []
end

@doc """    ThClass

A Class is just a Set that doesn't worry about foundations.

""" ThClass

@theory ThGraph <: ThClass begin
  Hom(dom::Ob, codom::Ob)::TYPE
  @op (→) := Hom
end

@theory ThLawlessCat <: ThGraph begin
  compose(f::(a → b), g::(b → c))::(a → c) ⊣ [(a,b,c)::Ob]
  @op (⋅) := compose
end

@doc """    ThLawlessCat

The data of a category without any axioms of associativity or identities.
""" ThLawlessCat

@theory ThAscCat <: ThLawlessCat begin
  assoc := ((f ⋅ g) ⋅ h) == (f ⋅ (g ⋅ h)) :: Hom(a,d) ⊣
    [a::Ob, b::Ob, c::Ob, d::Ob, f::Hom(a,b), g::Hom(b,c), h::Hom(c,d)]
end

@doc """    ThAscCat

The theory of a category with the associative law for composition.
""" ThAscCat

@theory ThIdLawlessCat <: ThAscCat begin
  id(a::Ob)::Hom(a,a)
end

@doc """    ThIdLawlessCat

The theory of a category without identity axioms.
""" ThIdLawlessCat

@theory ThCategory <: ThIdLawlessCat begin
  idl := id(a) ⋅ f == f :: Hom(a,b) ⊣ [a::Ob, b::Ob, f::Hom(a,b)]
  idr := f ⋅ id(b) == f :: Hom(a,b) ⊣ [a::Ob, b::Ob, f::Hom(a,b)]
end

@doc """    ThCategory

The theory of a category with composition operations and associativity and identity axioms.
""" ThCategory

@theory ThThinCategory <: ThCategory begin
  thineq := f == g :: Hom(A,B) ⊣ [A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B)]
end

@doc """    ThThinCategory

The theory of a thin category meaning that if two morphisms have the same domain and codomain they are equal as morphisms.
These are equivalent to preorders.
""" ThThinCategory
end
