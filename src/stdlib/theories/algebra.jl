export ThEmpty, ThSet, ThMagma, ThSemiGroup, ThMonoid, ThGroup, ThCMonoid, ThAb, ThSemiRing, ThRing, ThCRing, ThBooleanRing, ThDivisionRing, ThField, ThCRig, ThElementary, ThPreorder, ThLeftModule, ThRightModule, ThBiModule, ThModule, ThCommRMod

import Base: +, *, zero, one

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

# TODO test theory equality
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
# best to export default as K or something
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


# THEORIES OVER TWO SORTS

# @theory ThMod begin 
#   using ThAb: default as M =turnsinto=> import ThAb; @op M := ThAb.default
# end

@theory ThLeftModule begin
  using ThAb: default as M, ⋅ as ⊕
  using ThRing: default as Scalar, one as unit  

  (r ⋅ a) :: M ⊣ [r::Scalar, a::M]                                    # R-actions
  (r ⋅ (a ⊕ b)) == ((r ⋅ a) ⊕ (r ⋅ b)) ⊣ [r::Scalar, a::M, b::M]      # R-action left-distributes
  ((r + s) ⋅ a) == ((r ⋅ a) ⊕ (s ⋅ a)) ⊣ [r::Scalar, s::Scalar, a::M] # addition of R-actions 
  (r * s) ⋅ a == r ⋅ (s ⋅ a) ⊣ [r::Scalar, s::Scalar, a::M]           # composition of R-action
  unit ⋅ a == a ⊣ [unit::Scalar, a::M]                                # unit 
end

@theory ThRightModule begin
  using ThAb: default as M, ⋅ as ⊕
  using ThRing: default as Scalar, one as unit

  (a ⋅ r) :: M ⊣ [r::Scalar, a::M]                                    # R-actions
  ((a ⊕ b) ⋅ r) == ((a ⋅ r) ⊕ (b ⋅ r)) ⊣ [r::Scalar, a::M, b::M]      # R-action left-distributes
  (a ⋅ (r + s)) == ((a ⋅ r) ⊕ (a ⋅ s)) ⊣ [r::Scalar, s::Scalar, a::M] # addition of R-actions 
  a ⋅ (r * s) == (a ⋅ r) ⋅ s ⊣ [r::Scalar, s::Scalar, a::M]           # composition of R-action
  a ⋅ unit  == a ⊣ [unit::Scalar, a::M]                               # unit 
end

# XXX this exists because we need to fix a issue where terms with the same name have different idents
@theory ThModule begin
  using ThAb: default as M, ⋅ as ⊕
  using ThRing: default as Scalar, one as unit

  (r ⋅ a) :: M ⊣ [r::Scalar, a::M]                                    # R-actions
  (r ⋅ (a ⊕ b)) == ((r ⋅ a) ⊕ (r ⋅ b)) ⊣ [r::Scalar, a::M, b::M]      # R-action left-distributes
  ((r + s) ⋅ a) == ((r ⋅ a) ⊕ (s ⋅ a)) ⊣ [r::Scalar, s::Scalar, a::M] # addition of R-actions 
  (r * s) ⋅ a == r ⋅ (s ⋅ a) ⊣ [r::Scalar, s::Scalar, a::M]           # composition of R-action
  unit ⋅ a == a ⊣ [unit::Scalar, a::M]                                # unit

  (a ⋅ r) :: M ⊣ [r::Scalar, a::M]                                    # R-actions
  ((a ⊕ b) ⋅ r) == ((a ⋅ r) ⊕ (b ⋅ r)) ⊣ [r::Scalar, a::M, b::M]      # R-action left-distributes
  (a ⋅ (r + s)) == ((a ⋅ r) ⊕ (a ⋅ s)) ⊣ [r::Scalar, s::Scalar, a::M] # addition of R-actions 
  a ⋅ (r * s) == (a ⋅ r) ⋅ s ⊣ [r::Scalar, s::Scalar, a::M]           # composition of R-action
  a ⋅ unit  == a ⊣ [unit::Scalar, a::M]                               # unit
end

# TODO gensymming afoot
@theory ThBiModule begin
  using ThLeftModule: Scalar as LeftScalar
  using ThRightModule: Scalar as RightScalar
end
# TODO in this case, 
#   1. ThRightModule and ThLeftModule both rename default to M, which gets a newscopetag, since
#     1.a: it does not exist in the new theory
#     1.b: it does not exist in the old theory
#   2. ThBiModule contributes both Left and Right Modules. Since the scalars are being renamed (to the same name), they are checked if they have new 

# TODO we do not change the idents, so M and Scalar show
# @theory __ThModule begin
#   using ThLeftModule
#   using ThRightModule
# end

# @theory ThVectorSpace begin
#   using ThModule: M as V
#   # using ThField: default as K
# end

# TODO Fix axioms
# @theory ThCommRMod begin
#   using ThLeftModule
#   x + y == y + x ⊣ [x::Scalar, y::Scalar]
# end

## bilinear operation is given by ⋅ but should be ⊕
#@theory ThDistributiveAlgebra begin
#  using ThCommRMod
#  #
#  (x ⊕ y) ⋅ z == (x ⋅ z) ⊕ (y ⋅ z) ⊣ [x::M, y::M, z::M]
#  x ⋅ (y ⊕ z) == (x ⋅ y) ⊕ (x ⋅ z) ⊣ [x::M, y::M, z::A]
#  (r ⋅ x) ⋅ (s ⋅ y) == (r ⋅ s) ⋅ (x ⋅ y) ⊣ [r::R, s::R, x::M, y::M]
#end

# @theory ThAlternativeAlgebra begin
#   using ThDistributiveAlgebra

#   x * (x * y) == (x * x) * y ⊣ [x::M, y::M]
#   (y * x) * x == y * (x * x) ⊣ [x::M, y::M]
# end

