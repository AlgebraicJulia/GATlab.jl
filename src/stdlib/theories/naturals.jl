export ThNat, ThNatPlus, ThNatPlusTimes

import Base: +

""" The theory of natural numbers

"""
@theory ThNat begin
  ℕ :: TYPE
  Z :: ℕ
  S(n::ℕ) :: ℕ
end

""" The theory of natural numbers with addition as repeated succession

"""
@theory ThNatPlus <: ThNat begin
  using ThNat
  ((x::ℕ) + (y::ℕ))::ℕ
  (n + S(m) == S(n+m) :: ℕ) ⊣ [n::ℕ,m::ℕ]
end

""" The theory of nat-plus with multiplication

"""
@theory ThNatPlusTimes <: ThNatPlus begin
  using ThNatPlus
  ((x::ℕ) * (y::ℕ))::ℕ
  (n * S(m) == ((n * m) + n)) ⊣ [n::ℕ,m::ℕ]
end
