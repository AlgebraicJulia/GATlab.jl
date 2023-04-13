module Naturals

# Natural numbers

@theory ThNat <: ThEmpty begin
  ℕ :: TYPE ⊣ []
  Z() :: ℕ ⊣ []
  S(n) ::  ℕ ⊣ [n::ℕ]
end

@theory ThNatPlus <: ThNat begin
  (x + y)::ℕ ⊣ [x::ℕ, y::ℕ]
  (n + S(m) == S(n+m) :: ℕ) ⊣ [n::ℕ,m::ℕ]
end

@theory ThNatPlusTimes <: ThNatPlus begin
  (x * y)::ℕ ⊣ [x::ℕ, y::ℕ]
  (n * S(m) == ((n * m) + n) :: ℕ) ⊣ [n::ℕ,m::ℕ]
end

"""
@instance NatPlusIsMonoid{ThMonoid, ThNatPlus}
  Ob = ℕ
  x ∘ y = x + y
  e() = Z()
end

@instance Swap{ThMonoid,ThMonoid}
  Ob = Ob
  ∘(x, y) = y ∘ x
  e() = e()
end

@instance CatIsPreorder{ThCategory,ThPreorder}
  Ob = Ob
  Hom = Leq
  ⋅(a,b) = trans(a,b)
  id(a) = refl(a)
end
"""

end
