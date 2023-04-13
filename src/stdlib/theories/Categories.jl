module Categories
export ThClass, ThGraph, ThLawlessCat, ThAscCat, ThCategory, ThPreorder,
        ThMagma, ThSemiGroup, ThMonoid, ThGroup,
        ThNat, ThNatPlus, ThNatPlusTimes

using ....Dsl
using ....Syntax: ThEmpty

# Category theory
@theory ThClass <: ThEmpty begin
  Ob::TYPE ⊣ []
end

@theory ThGraph <: ThClass begin
  Hom(dom,codom)::TYPE ⊣ [dom::Ob, codom::Ob]
end

@theory ThLawlessCat <: ThGraph begin
  (f ⋅ g)::Hom(a,c) ⊣ [a::Ob, b::Ob, c::Ob, f::Hom(a,b), g::Hom(b,c)]
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

end
