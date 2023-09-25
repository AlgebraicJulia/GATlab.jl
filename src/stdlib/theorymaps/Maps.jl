module Maps

export SwapMonoid, NatPlusMonoid, PreorderCat, OpCat

using ...StdTheories
using ....Syntax


@theorymap SwapMonoid(ThMonoid, ThMonoid) begin
  default => default
  x⋅y ⊣ [x, y] => y⋅x
  e => e
end

@theorymap NatPlusMonoid(ThMonoid, ThNatPlus)  begin
  default => ℕ 
  e => Z
  (x ⋅ y) ⊣ [x, y] => x+y
end

@theorymap OpCat(ThCategory, ThCategory) begin
  Ob => Ob
  Hom(dom::Ob, codom::Ob) => Hom(codom, dom)
  id(a::Ob) => id(a)
  compose(f::Hom(a,b), g::Hom(b,c)) ⊣ [(a,b,c)::Ob] => compose(g, f)
end

"""Preorders are categories"""
@theorymap PreorderCat(ThCategory, ThPreorder) begin
  Ob => default
  Hom(dom::Ob, codom::Ob) => Leq(dom, codom)
  compose(f::(a → b), g::(b → c)) ⊣ [a::Ob, b::Ob, c::Ob] => trans(f, g)
  id(a) ⊣ [a::Ob] => refl(a)
end

"""Thin categories are isomorphic to preorders"""
# PreorderThinCat = @compose(PreorderCat, Incl(ThCategory, ThThinCategory))
# ThinCatPreorder = @inv(PreorderThinCat)


end # module
