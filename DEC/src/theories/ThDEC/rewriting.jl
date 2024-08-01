using Metatheory
using Metatheory.Library

ThMultiplicativeMonoid = @commutative_monoid (*) 1
ThAdditiveGroup = @commutative_group (+) 0 (-)
Distributivity = @distrib (*) (+)
ThRing = ThMultiplicativeMonoid ∪ ThAdditiveGroup ∪ Distributivity 

Derivative = @theory (f, g)::Function, a::Scalar begin
  f * d(g) + d(f) * g --> d(f * g)
  d(f) + d(g) --> d(f + g)
  d(a * f) --> a * d(f)
end


# e = :(f * d(g) + d(f) * g)
# g = EGraph(e)
# saturate!(g, product)
# extract!(g, astsize)

zero = @theory f begin
  f * 0 --> 0
  f + 0 --> f
  0 + f --> f
end

square_zero = @theory ω begin
  d(d(ω)) --> 0
end

linearity = @theory f g a begin
  Δ(f + g) == Δ(f) + Δ(g)
  Δ(a * f) == a * Δ(f)
end
export linearity

