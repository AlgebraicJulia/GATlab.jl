module Categories
export ThClass, ThGraph, ThLawlessCat, ThAscCat, ThCategory, ThThinCategory

using ....Syntax

# Category theory
@theory ThClass begin
  Ob::TYPE ⊣ []
end

@theory ThGraph <: ThClass begin
  Hom(dom::Ob, codom::Ob)::TYPE
  @op (→) := Hom
end

@theory ThLawlessCat <: ThGraph begin
  compose(f::(a → b), g::(b → c))::(a → c) ⊣ [(a,b,c)::Ob]
  @op (⋅) := compose
end

@theory ThAscCat <: ThLawlessCat begin
  assoc := ((f ⋅ g) ⋅ h) == (f ⋅ (g ⋅ h)) :: Hom(a,d) ⊣
    [a::Ob, b::Ob, c::Ob, d::Ob, f::Hom(a,b), g::Hom(b,c), h::Hom(c,d)]
end

@theory ThIdLawlessCat <: ThAscCat begin
  id(a::Ob)::Hom(a,a)
end

@theory ThCategory <: ThIdLawlessCat begin
  idl := id(a) ⋅ f == f :: Hom(a,b) ⊣ [a::Ob, b::Ob, f::Hom(a,b)]
  idr := f ⋅ id(b) == f :: Hom(a,b) ⊣ [a::Ob, b::Ob, f::Hom(a,b)]
end

@theory ThThinCategory <: ThCategory begin
  thineq := f == g :: Hom(A,B) ⊣ [A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B)]
end

end
