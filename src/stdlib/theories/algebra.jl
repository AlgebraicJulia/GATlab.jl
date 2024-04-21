export ThEmpty, ThSet, ThMagma, ThSemiGroup, ThMonoid, ThGroup, ThCMonoid, ThAb, ThRing,
  ThCRing, ThRig, ThCRig, ThElementary, ThPreorder

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

""" The theory of a semiring

A set where addition is a commutative monoid, multiplication is monoidal, and they interact through distributivity.

Examples:
  - 

"""
@theory ThSemiRing begin
  using ThCMonoid: ⋅ as +, e as zero
  using ThMonoid: ⋅ as *, e as one
  x * (y + z) == (x * y) + (x * y) ⊣ [x,y,z]
end

@theory ThRig begin
  using ThSemiRing
end

""" The theory of a ring

A set where addition is a group, multiplication is monoidal, and they interact through distributivity.

Examples:
  - 

A ring can also be obtaned by imposing additive inverses on a semiring.
"""
@theory ThRing begin
  using ThAb: ⋅ as +, i as -, e as zero
  using ThMonoid: ⋅ as *, e as one
  x * (y + z) == (x * y) + (x * z) ⊣ [x,y,z]
end

""" The theory of a ring where multiplicative is commutative.

Examples:
  - 

"""
@theory ThCRing begin
  using ThRing
  x * y == y * x ⊣ [x,y]
end

""" The theory of a commutative ring with multiplicative idempotence.

Examples:
  - 

"""
@theory ThBooleanRing begin
  using ThCRing
  x * x == x ⊣ [x]
end

""" The theory of a ring with multiplicative inverses 

 - The set of Quarternions ℍ 

"""
@theory ThDivisionRing begin
  using ThRing
  i(x) :: default ⊣ [x]
  i(x) * x == one() ⊣ [x]
  x * i(x) == one() ⊣ [x]
end

# TODO: how to handle cases where RHS of axiom must be a different sort (e.g., nonzero) than those on the LHS (e.g., default)? Can we define a sort which inherits axioms defined on another sort (default)?
""" The theory of a commutative ring where multiplication by nonzero elements is nonzero 

 - 

"""
# @theory ThIntegralDomain begin
#   using ThCRing
#   nonzero::TYPE
#   # using ThCRing: default as nonzero
#   x * y == z ⊣ [x::nonzero, y::nonzero, z::nonzero]
# end

# using two theories which overlap considerably, we can still add unique elem 
""" The theory of a commutative division ring

 - The rational numbers ℚ and algebraic extensions, i.e. ℚ[√2]
 - The real numbers ℝ and its algebraic completion, the complex numbers ℂ
 - 

"""
@theory ThField begin
  using ThDivisionRing
  using ThCRing
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


# ALGEBRA OVER TWO SETS

# using two plus signs, oops! can we overload plus signs?
@theory ThModule begin
  using ThAb: default as M, ⋅ as ⊕
  using ThRing: default as R, one as unit 
  
  (r ⋅ a) :: M ⊣ [r::R, a::M]
  (r ⋅ (a ⊕ b)) == ((r ⋅ a) ⊕ (r ⋅ b)) ⊣ [r::R, a::M, b::M]
  ((r + s) ⋅ a) == ((r ⋅ a) ⊕ (s ⋅ a)) ⊣ [r::R, s::R, a::M]
  (r*s) ⋅ a == r ⋅ (s ⋅ a) ⊣ [r::R, s::R, a::M]
  unit ⋅ a == a ⊣ [unit::R, a::M]
end

@theory ThVectorSpace begin
  using ThModule
  using ThField 
end

@theory ThCommutativeRModule begin
  using ThModule
  using ThCRing: default as R, one as unit
end

## bilinear operation is given by ⋅ but should be ⊕
# @theory ThDistributiveAlgebra begin
#   using ThCommutativeRModule: M as A

#   (x + y) ⋅ z == (x ⋅ z) + (y ⋅ z) ⊣ [x::A, y::A, z::A]
#   x ⋅ (y + z) == (x ⋅ y) + (x ⋅ z) ⊣ [x::A, y::A, z::A]
#   (r ⋅ x) ⋅ (s ⋅ y) == (r ⋅ s) ⋅ (x ⋅ y) ⊣ [r::R, s::R, x::A, y::A]
# end

#@theory ThAlternativeAlgebra begin
#  using ThCommutativeRModule

#  x ⋅ (x ⋅ y) == (x ⋅ x) ⋅ y ⊣ [x::M, y::M]
#  (y ⋅ x) ⋅ x == y ⋅ (x ⋅ x) ⊣ [x::M, y::M]
#end

## 
#@theory ThCompositionAlgebra begin
#  using ThDistributiveAlgebra: 

#  # nondegenerate p.d. quadratic form
#  N(x) :: A ⊣ [x::A]
#  N(x⋅y) == N(x)⋅N(y) ⊣ [x::A, y::A]

#  x ⟧ y == N(x + y) - N(x) - N(y) ⊣ [x::A]
#end

#@theory ThLieAlgebra begin
#  using ThDistributiveAlgebra: A as 𝔤

#  x ⟦ y :: A ⊣ [(x,y)::𝔤]
#  (a*x + b*y) ⟦ z == a ⋅ (x ⟦ z) + b ⋅ (y ⟦ z) ⊣ [(a,b)::K, (x,y,z)::𝔤]
#  z ⟦ (a*x + b*y) == a ⋅ (z ⟦ x) + b ⋅ (z ⟦ y) ⊣ [(a,b)::K, (x,y,z)::𝔤]
  
#  x ⟦ x == zero ⊣ [x::𝔤]

#  (x ⟦ (y ⟦ z)) + (y ⟦ (z ⟦ x)) + (z ⟦ (x ⟦ y)) == zero ⊣ [(x,y,z)::𝔤]
#end

## @theory ThJordanAlgebra begin
#  # using ThDistributiveAlgebra

#  # commutativity
#  # (x⋅y)

#""" The theory of associative algebras

#"""
#@theory ThAlgebra begin
#  using ThDistributiveAlgebra

#  (x ⋅ (y ⋅ z)) == (x ⋅ (y ⋅ z)) ⊣ [x::M, y::M, z::M]
#end

#@theory ThStarAlgebra begin
#  using ThAlgebra

#  †(x) :: A ⊣ [x::A]
#  †(x + y) == †(x) + †(y) ⊣ [x::A, y::A]
#  †(one) == one
#  †(†(x)) = x ⊣ [x::A]
#end
## scalars must be commutative

## what is the 1ₓ? can we axiomatically build "co" theories?
#@theory ThCoAlgebra begin
#  using ThVectorSpace: M as V

#  Δ(x) == x ⊗ x ⊣ [x::V]
#  ϵ(x) :: K ⊣ [x::V]
#  (1ₓ ⊗ Δ(x))(Δ(x)) == (Δ ⊗ 1ₓ)(Δ(x)) ⊣ [x::V]
#end


## TODO need to add compatibility conditions
#@theory ThBiAlgebra begin
#  using ThAlgebra: default as B, ⋅ as ∇
#  using ThCoAlgebra: default as B
#end

#@theory ThHopfAlgebra begin
#  using ThBiAlgebra 

#  # need to specify what it means to be K-linear
#  S(x) :: B ⊣ [x::B]
#  S(k⋅ x) == k⋅S(x) ⊣ [k::K, x::B]
#  # can I omit the scalar term? can I do (k₁,k₂)::K a la Decapodes?
#  S(k₁⋅x₁ + k₂⋅x₂) == S(k₁⋅x₁) + S(k₂⋅x₂) ⊣ [k₁::K,k₂::K,x₁::B,x₂::B]

#  # antipodal relations
#  ∇((S ⊗ 1ₓ)(Δ(x))) == η(ϵ(x)) ⊣ [x::B]
#  ∇((1ₓ ⊗ S)(Δ(x))) == η(ϵ(x)) ⊣ [x::B]
#end





## need conjugate symmetry, linearity, p.d.
#@theory ThInnerProductSpace begin
#  using ThVectorSpace: M as V

#  x ⟧ y :: K ⊣ [x::V, y::V]
#end

# 
