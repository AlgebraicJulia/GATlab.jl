module Algebra
export ThEmpty, ThSet, ThMagma, ThSemiGroup, ThMonoid, ThGroup, ThCMonoid, ThAb, ThRing,
  ThCRing, ThRig, ThCRig, ThElementary, ThPreorder

using ....Syntax

@theory ThEmpty begin 
end

@theory ThSet begin
  default::TYPE
end

@theory ThMagma <: ThSet begin
  (x ⋅ y) :: default
end

@theory ThSemiGroup <: ThMagma begin
  (x ⋅ y) ⋅ z == (x ⋅ (y ⋅ z)) ⊣ [x, y, z]
end

@theory ThMonoid <: ThSemiGroup begin
  e :: default
  e ⋅ x == x ⊣ [x]
  x ⋅ e == x ⊣ [x]
end

@theory ThGroup <: ThMonoid begin
  i(x)
  i(x) ⋅ x == e ⊣ [x]
  x ⋅ i(x) == e ⊣ [x]
end

@theory ThCMonoid <: ThMonoid begin
  a ⋅ b == b ⋅ a ⊣ [a, b]
end

# @theory ThAb <: ThMonoid begin
#   using ThGroup
#   using ThCMonoid
# end

# @theory ThRing <: ThSet begin
#   using ThAb: ⋅ as +, i as -, e as zero
#   using ThMonoid: ⋅ as *, e as one
#   a * (b + c) == (a * b) + (a * c) ⊣ [a,b,c]
# end

# @theory ThCRing <: ThRing begin
#   a * b == b * a ⊣ [a,b]
# end

# @theory ThRig <: ThSet begin
#   using ThCMonoid: ⋅ as +, e as zero
#   using ThMonoid: ⋅ as *, e as one
#   a * (b + c) == (a * b) + (a * c) ⊣ [a,b,c]
# end

# @theory ThCRig <: ThRig begin
#   a * b == b * a ⊣ [a,b]
# end

# @theory ThElementary <: ThCRing begin
#   sin(x) ⊣ [x]
#   cos(x) ⊣ [x]
#   tan(x) ⊣ [x]
#   exp(x) ⊣ [x]
#   sigmoid(x) ⊣ [x]
# end

@theory ThPreorder <: ThSet begin
  Leq(dom, codom)::TYPE
  @op (≤) := Leq
  refl(p)::Leq(p,p)
  trans(f::Leq(p,q),g::Leq(q,r))::Leq(p,r)  ⊣ [p,q,r]
  irrev := f == g ::Leq(p,q) ⊣ [p,q, (f,g)::Leq(p,q)]
end

end
