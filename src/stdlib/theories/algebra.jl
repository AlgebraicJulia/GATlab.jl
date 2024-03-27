export ThEmpty, ThSet, ThMagma, ThSemiGroup, ThMonoid, ThGroup, ThCMonoid, ThAb, ThRing,
  ThCRing, ThRig, ThCRig, ThElementary, ThPreorder,
  TheMagma, TheSemiGroup, TheMonoid

@theory ThEmpty begin
end

@theory ThSet begin
  default::TYPE
end

@theory TheMagma begin
  using ThSet
  (x ⋅ y) :: default ⊣ [x, y]
end

@theory ThMagma begin
  using ThSet
  (x ⋅ y) :: default ⊣ [x, y]
end

@theory TheSemiGroup begin
  using TheMagma
  (x ⋅ y) ⋅ z == (x ⋅ (y ⋅ z)) ⊣ [x, y, z]
end

@theory ThSemiGroup begin
  using ThMagma
  (x ⋅ y) ⋅ z == (x ⋅ (y ⋅ z)) ⊣ [x, y, z]
end

@theory TheMonoid begin
  using TheSemiGroup
  e() :: default
  e() ⋅ x == x ⊣ [x]
  x ⋅ e() == x ⊣ [x]
end
# ERROR: LoadError: UndefVarError: `default` not defined
# Stacktrace:
#   [1] getproperty(x::Module, f::Symbol)
#     @ Base ./Base.jl:31
#   [2] macro expansion
#     @ ~/Documents/UFAJ/AlgebraicJulia/GATlab/GATlab.jl/src/models/ModelInterface.jl:701 [inlined]
#   [3] top-level scope
#     @ ~/Documents/UFAJ/AlgebraicJulia/GATlab/GATlab.jl/src/stdlib/derivedmodels/DerivedModels.jl:12
@theory ThMonoid begin
  using ThSemiGroup
  e() :: default
  e() ⋅ x == x ⊣ [x]
  x ⋅ e() == x ⊣ [x]
end

@theory TheGroup begin
  using TheMonoid
  i(x) :: default ⊣ [x]
  i(x) ⋅ x == e() ⊣ [x]
  x ⋅ i(x) == e() ⊣ [x]
end

@theory ThGroup <: ThMonoid begin
  i(x) :: default ⊣ [x]
  i(x) ⋅ x == e() ⊣ [x]
  x ⋅ i(x) == e() ⊣ [x]
end

@theory TheCMonoid begin
  using TheMonoid
  a ⋅ b == b ⋅ a ⊣ [a, b]
end

@theory ThCMonoid <: ThMonoid begin
  a ⋅ b == b ⋅ a ⊣ [a, b]
end

@theory ThAb <: ThMonoid begin
  using ThGroup
  using ThCMonoid
end

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
  Leq(dom, codom)::TYPE ⊣ [dom, codom]
  @op (≤) := Leq
  refl(p)::Leq(p,p) ⊣ [p]
  trans(f::Leq(p,q),g::Leq(q,r))::Leq(p,r)  ⊣ [p,q,r]
  irrev := f == g ⊣ [p,q, (f,g)::Leq(p,q)]
end
