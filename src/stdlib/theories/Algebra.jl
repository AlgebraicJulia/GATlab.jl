module Algebra
export ThSet, ThMagma, ThSemiGroup, ThMonoid, ThGroup, ThCMonoid, ThAb, ThRing, ThCRing

using ....Dsl
using ....Syntax: ThEmpty

@theory ThSet <: ThEmpty begin
  default::TYPE
end

@theory ThMagma <: ThSet begin
  (x ⋅ y) ⊣ [x,y]
end

@theory ThSemiGroup <: ThMagma begin
  (x ⋅ y) ⋅ z == (x ⋅ (y ⋅ z)) ⊣ [x,y,z]
end

@theory ThMonoid <: ThSemiGroup begin
  e() ⊣ []
  e() ⋅ x == x ⊣ [x]
  x ⋅ e() == x ⊣ [x]
end

@theory ThGroup <: ThMonoid begin
  i(x) ⊣ [x]
  i(x) ⋅ x == e ⊣ [x]
  x ⋅ i(x) == e ⊣ [x]
end

@theory ThCMonoid <: ThMonoid begin
  a ⋅ b == b ⋅ a ⊣ [a,b]
end

@theory ThAb <: ThMonoid begin
  using ThGroup
  using ThCMonoid
end

@theory ThRing <: ThSet begin
  using ThAb: ⋅ as +, i as -, e as 0
  using ThMonoid: ⋅ as *, e as 1
  a * (b + c) == (a * b) + (a * c) ⊣ [a,b,c]
end

@theory ThCRing <: ThRing begin
  a * b == b * a ⊣ [a,b]
end

@theory ThRig <: ThSet begin
  using ThCMonoid: ⋅ as +, e as 0
  using ThMonoid: ⋅ as *, e as 1
  a * (b + c) == (a * b) + (a * c) ⊣ [a,b,c]
end

@theory ThCRig <: ThRig begin
  a * b == b * a ⊣ [a,b]
end

end
