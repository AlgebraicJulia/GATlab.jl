module Maps

export SwapMonoid, NatPlusMonoid, PreorderCat, OpCat

using ...StdTheories
using ....Syntax

@theorymap SwapMonoid(ThMonoid, ThMonoid) begin
  default => default
  x⋅y ⊣ [x, y] => y⋅x
  e() => e()
end

@theorymap NatPlusMonoid(ThMonoid, ThNatPlus)  begin
  default => ℕ 
  e() => Z()
  (x ⋅ y) ⊣ [x, y] => x+y
end

@theorymap OpCat(ThCategory, ThCategory) begin
  Ob => Ob
  Hom(dom, codom) ⊣ [dom::Ob, codom::Ob] => Hom(codom, dom)
  id(a) ⊣ [a::Ob] => id(a)
  compose(f,g) ⊣ [(a,b,c)::Ob, f::Hom(a,b), g::Hom(b,c)] => compose(g, f)
end

"""Preorders are categories"""
@theorymap PreorderCat(ThCategory, ThPreorder) begin
  Ob => default
  Hom(dom, codom) ⊣ [dom::Ob, codom::Ob] => Leq(dom, codom)
  compose(f, g) ⊣ [a::Ob, b::Ob, c::Ob, f::(a → b), g::(b → c)] => trans(f, g)
  id(a) ⊣ [a::Ob] => refl(a)
end

"""Thin categories are isomorphic to preorders"""
# PreorderThinCat = @compose(PreorderCat, Incl(ThCategory, ThThinCategory))
# ThinCatPreorder = @inv(PreorderThinCat)


end # module
