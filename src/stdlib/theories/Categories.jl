module Categories
export ThClass, ThGraph, ThLawlessCat, ThAscCat, ThCategory, ThPreorder,
        ThMagma, ThSemiGroup, ThMonoid, ThGroup,
        ThNat, ThNatPlus, ThNatPlusTimes,
        TypedHom

using ....Dsl
using ....Syntax: ThEmpty

# Category theory
@theory ThClass <: ThEmpty begin
  Ob::TYPE ⊣ []
end

@theory ThGraph <: ThClass begin
  Hom(dom,codom)::TYPE ⊣ [dom::Ob, codom::Ob]
  @op (→) := Hom
end

@theory ThLawlessCat <: ThGraph begin
  compose(f, g)::Hom(a,c) ⊣ [a::Ob, b::Ob, c::Ob, f::Hom(a,b), g::Hom(b,c)]
  @op begin
    (⋅) := compose
  end
end

@theory ThAscCat <: ThLawlessCat begin
  assoc := ((f ⋅ g) ⋅ h) == (f ⋅ (g ⋅ h)) :: Hom(a,d) ⊣ [a::Ob, b::Ob, c::Ob, d::Ob, f::Hom(a,b), g::Hom(b,c), h::Hom(c,d)]
end

@theory ThIdLawlessCat <: ThAscCat begin
  id(a)::Hom(a,a) ⊣ [a::Ob]
end

@theory ThCategory <: ThIdLawlessCat begin
  idl := id(a) ⋅ f == f :: Hom(a,b) ⊣ [a::Ob, b::Ob, f::Hom(a,b)]
  idr := f ⋅ id(b) == f :: Hom(a,b) ⊣ [a::Ob, b::Ob, f::Hom(a,b)]
end

@theory ThThinCategory <: ThCategory begin
  thineq := f == g :: Hom(A,B) ⊣ [A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B)]
end

"""
Any implementor of TypedHom{Ob, Hom} should have precisely the fields

- dom::Ob
- codom::Ob
- morphism::Hom

The reason this is not a struct is that we want to be able to control
the name of the type.
"""
abstract type TypedHom{Ob, Hom} end

end
