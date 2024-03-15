export ThEmpty, ThSet, ThMagma, ThSemiGroup, ThMonoid, ThGroup, ThCMonoid, ThAb, ThRing,
  ThCRing, ThRig, ThCRig, ThElementary, ThPreorder

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
@theory ThMagma <: ThSet begin
  (x ⋅ y) :: default ⊣ [x, y]
end

""" This theory contains an associative binary operation called multiplication. 

Examples:
  - The integers under multiplication
  - Nonempty lists under concatenation
"""
@theory ThSemiGroup <: ThMagma begin
  (x ⋅ y) ⋅ z == (x ⋅ (y ⋅ z)) ⊣ [x, y, z]
end

""" The theory of a semigroup with identity.

Examples:
  - The integers under multiplication
  - Lists (nonempty and empty) under concatenation
"""
@theory ThMonoid <: ThSemiGroup begin
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
@theory ThGroup <: ThMonoid begin
  i(x) :: default ⊣ [x]
  i(x) ⋅ x == e() ⊣ [x]
  x ⋅ i(x) == e() ⊣ [x]
end

""" The theory of a monoid where multiplication enjoys commutativity.

Examples:
  - The set of classical 1-knots under "knot sum"
"""
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
