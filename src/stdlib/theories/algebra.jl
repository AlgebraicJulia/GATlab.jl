export ThEmpty, ThSet, ThMagma, ThSemiGroup, ThMonoid, ThGroup, ThCMonoid, ThAb, ThSemiRing, ThRing, ThCommRing, ThDiffRing, ThBooleanRing, ThDivisionRing, ThCRig, ThElementary, ThPreorder, ThLeftModule, ThRightModule, ThModule, ThCommRModule

import Base: +, *, zero, one

@theory ThEmpty begin
end

""" The theory of a set with no operations

A base theory for all algebraic theories so that multiple
inheritance doesn't create multiple types.
"""
@theory ThSet begin
  default::TYPE
end

""" The theory of a set with a binary operation which does not guarantee associativity

Examples:
  - The integers with minus operation is not associative.

    (a ⋅ b) ⋅ c = a - b - c

    a ⋅ (b ⋅ c) = a - b + c 

"""
@theory ThMagma begin
  using ThSet
  (x ⋅ y) :: default ⊣ [x, y]
end

""" This theory contains an associative binary operation called multiplication. 

Examples:
  - The integers under multiplication
  - Nonempty lists under concatenation
"""
@theory ThSemiGroup begin
  using ThMagma
  (x ⋅ y) ⋅ z == (x ⋅ (y ⋅ z)) ⊣ [x, y, z]
end

""" The theory of a semigroup with identity.

Examples:
  - The integers under multiplication
  - Lists (nonempty and empty) under concatenation
"""
@theory ThMonoid begin
  using ThSemiGroup
  e() :: default
  e() ⋅ x == x ⊣ [x]
  x ⋅ e() == x ⊣ [x]
end

""" The theory of a monoid with multiplicative inverse.

Examples:
  - The rationals (excluding zero) under multiplication
  - E(n), the group of rigid transformations (translation and rotation)
  - Bₙ, the braid group of n strands
"""
@theory ThGroup begin
  using ThMonoid
  i(x) :: default ⊣ [x]
  i(x) ⋅ x == e() ⊣ [x]
  x ⋅ i(x) == e() ⊣ [x]
end

""" The theory of a monoid where multiplication enjoys commutativity.

Examples:
  - The set of classical 1-knots under "knot sum"
"""
@theory ThCMonoid begin
  using ThMonoid
  a ⋅ b == b ⋅ a ⊣ [a, b]
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
@theory ThCommRing begin
  using ThRing
  x * y == y * x ⊣ [x,y]
end

"""
A commutative ring equipped with a *derivation* operator `d` which fulfills linearity and the Leibniz product rule.
"""
@theory ThDiffRing begin
  using ThCommRing
  d(x) :: default ⊣ [x::default]
  d(x + y) == d(x) + d(y) ⊣ [x::default, y::default]
  d(x*y) == d(x)*y + x*d(y) ⊣ [x::default, y::default]
end

""" The theory of a commutative ring with multiplicative idempotence.

Examples:
  - 

"""
@theory ThBooleanRing begin
  using ThCommRing
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

@theory ThCRig begin
  using ThRig
  a * b == b * a ⊣ [a,b]
end

@theory ThElementary begin
  using ThCommRing
  sin(x) ⊣ [x]
  cos(x) ⊣ [x]
  tan(x) ⊣ [x]
  exp(x) ⊣ [x]
  sigmoid(x) ⊣ [x]
end

# TODO @op does not get repr
""" The theory of sets which have a preorder.

This is equivalent to the theory of thin categories (`ThThinCategory`) where ≤ is the composition operation.

Examples:
  - The set of natural numbers ordered by b-a ≥ 0
  - The set of natural numbers ordered by "a divides b"
"""
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

# TODO Fix axioms
@theory ThCommRModule begin
  using ThModule
  x + y == y + x ⊣ [x::Scalar, y::Scalar]
end

## bilinear operation is given by ⋅ but should be ⊕
#@theory ThDistributiveAlgebra begin
#  using ThCommRModule
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

