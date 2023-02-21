module Theories
export ThSet, ThGraph, ThLawlessCat, ThAscCat, ThCategory,ThMagma,ThSemiGroup,
  ThMonoid,ThGroup,ThNat,ThNatPlus,ThNatPlusTimes

using ..GATs, ..Parse

# Category theory
@theory ThSet <: ThEmpty begin
  Ob::TYPE ⊣ []
end

@theory ThGraph <: ThSet begin
  Hom(a,b)::TYPE ⊣ [(a::Ob, b::Ob)]
end

@theory ThLawlessCat <: ThGraph begin
  (f ⋅ g)::Hom(a,c) ⊣ [(a::Ob, b::Ob, c::Ob), (f::Hom(a,b), g::Hom(b,c))]
end

@theory ThAscCat <: ThLawlessCat begin
  ((f ⋅ g) ⋅ h == (f ⋅ (g ⋅ h)) :: Hom(a,d)) ⊣ [(a::Ob, b::Ob, c::Ob, d::Ob), (f::Hom(a,b), g::Hom(b,c), h::Hom(c,d))]
end

@theory ThIdLawlessCat <: ThAscCat begin
  id(a)::Hom(a,a) ⊣ [(a::Ob,)]
end

@theory ThCategory <: ThIdLawlessCat begin
  (id(a) ⋅ f == f :: Hom(a,b)) ⊣ [(a::Ob, b::Ob), (f::Hom(a,b),)]
  (f ⋅ id(b) == f :: Hom(a,b)) ⊣ [(a::Ob, b::Ob), (f::Hom(a,b),)]
end

# Abstract algebra
@theory ThMagma <: ThSet begin
  (x ∘ y)::Ob ⊣ [(x::Ob, y::Ob)]
end

@theory ThSemiGroup <: ThMagma begin
  ((x ∘ y) ∘ z == (x ∘ (y ∘ z)) :: Ob) ⊣ [(x::Ob, y::Ob, z::Ob)]
end

@theory ThMonoid <: ThSemiGroup begin
  e() :: Ob ⊣ []
  (e() ∘ x == x :: Ob) ⊣ [(x::Ob,)]
  (x ∘ e() == x :: Ob) ⊣ [(x::Ob,)]
end

@theory ThGroup <: ThMonoid begin
  i(x) :: Ob ⊣ [(x::Ob,)]
  (i(x) ∘ x == e :: Ob) ⊣ [(x::Ob,)]
  (x ∘ i(x) == e :: Ob) ⊣ [(x::Ob,)]
end

# Natural numbers 

@theory ThNat <: ThEmpty begin
  ℕ :: TYPE ⊣ []
  Z() :: ℕ ⊣ []
  S(n) ::  ℕ ⊣ [(n::ℕ,)]
end

@theory ThNatPlus <: ThNat begin
  (x + y)::ℕ ⊣ [(x::ℕ, y::ℕ)]
  (n + S(m) == S(n+m) :: ℕ) ⊣ [(n::ℕ,m::ℕ)]
end

@theory ThNatPlusTimes <: ThNatPlus begin
  (x * y)::ℕ ⊣ [(x::ℕ, y::ℕ)]
  (n * S(m) == ((n * m) + n) :: ℕ) ⊣ [(n::ℕ,m::ℕ)]
end

"""
@instance NatPlusIsMonoid{Monoid, NatPlus}
  Ob = ℕ
  ∘(x, y) = x + y
  e() = Z() 
end

@instance Swap{Monoid,Monoid}
  Ob = Ob
  ∘(x, y) = y ∘ x
  e() = e() 
end 
"""



end
