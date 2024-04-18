export ThEmpty, ThSet, ThMagma, ThSemiGroup, ThMonoid, ThGroup, ThCMonoid, ThAb, ThRing,
  ThCRing, ThRig, ThCRig, ThElementary, ThPreorder,
  TheMagma, TheSemiGroup, TheMonoid

@theory ThEmpty begin
end

@theory ThSet begin
  default::TYPE
end

@theory ThMagma begin
  using ThSet
  (x ⋅ y) :: default ⊣ [x, y]
end

@theory ThSemiGroup begin
  using ThMagma
  (x ⋅ y) ⋅ z == (x ⋅ (y ⋅ z)) ⊣ [x, y, z]
end

@theory ThMonoid begin
  using ThSemiGroup
  e() :: default
  e() ⋅ x == x ⊣ [x]
  x ⋅ e() == x ⊣ [x]
end

@theory ThGroup begin
  using ThMonoid
  i(x) :: default ⊣ [x]
  i(x) ⋅ x == e() ⊣ [x]
  x ⋅ i(x) == e() ⊣ [x]
end

# TODO if I instead write "a" and "b" for "x" and "y", I think GATlab should coerce "a" and "b" to be "x" and "y"
# it could do this by going into the args for all the axioms, determining the terms per TYPE, i.e.
# DEFAULT: [x,y,z]
@theory ThCMonoid begin
  using ThMonoid
  x ⋅ y == y ⋅ x ⊣ [x, y]
end

@theory ThAb begin
  using ThGroup
  using ThCMonoid
end

@theory ThSemiRing begin
  using ThCMonoid: ⋅ as +, e as zero
  using ThMonoid: ⋅ as *, e as one
  x * (y + z) == (x * y) + (x * y) ⊣ [x,y,z]
end

# A ring can be obtained from a semiring by including additive inverse, or this way:
@theory ThRing begin
  using ThAb: ⋅ as +, i as -, e as zero
  using ThMonoid: ⋅ as *, e as one
  x * (y + z) == (x * y) + (x * y) ⊣ [x,y,z]
end

@theory ThCRing begin
  using ThRing
  x * y == y * x ⊣ [x,y]
end

@theory ThBooleanRing begin
  using ThCRing
  x * x == x ⊣ [x]
end

""" 

 - Quarternions

"""
@theory ThDivisionRing begin
  using ThRing
  i(x) :: default ⊣ [x]
  i(x) * x == one() ⊣ [x]
  x * i(x) == one() ⊣ [x]
end

@theory ThIntegralDomain begin
  using ThCRing
  nonzero::TYPE
  # using ThCRing: default as nonzero
  x * y == z ⊣ [x::default, y::default, z::nonzero]
end

# @theory ThField begin
#   using ThDivisionRing
#   using ThCRing
# end

@theory ThRig begin
  using ThCMonoid: ⋅ as +, e as zero
  using ThMonoid: ⋅ as *, e as one
  a * (b + c) == (a * b) + (a * c) ⊣ [a,b,c]
end

@theory ThCRig begin
  using ThRig
  a * b == b * a ⊣ [a,b]
end


@theory ThElementary begin
  using ThCRing
  sin(x) ⊣ [x]
  cos(x) ⊣ [x]
  tan(x) ⊣ [x]
  exp(x) ⊣ [x]
  sigmoid(x) ⊣ [x]
end

@theory ThPreorder <: ThSet begin
  Leq(dom, codom)::TYPE ⊣ [dom, codom]
  @op (≤) := Leq
  refl(p)::Leq(p,p) ⊣ [p]
  trans(f::Leq(p,q),g::Leq(q,r))::Leq(p,r)  ⊣ [p,q,r]
  irrev := f == g ⊣ [p,q, (f,g)::Leq(p,q)]
end

# @theory ThKleene begin
#   using ThPreorder
#   using ThSemiRing
#   x + x == x ⊣ [x]
#   ⋆(x)::default
#   1 + ⋆(x)*x ≤ ⋆(x) ⊣ [x]
#   1 + x*⋆(x) ≤ ⋆(x) ⊣ [x]



