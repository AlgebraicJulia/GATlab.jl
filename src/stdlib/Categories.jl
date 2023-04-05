module Categories
export ThSet, ThGraph, ThLawlessCat, ThAscCat, ThCategory, ThPreorder,
        ThMagma, ThSemiGroup, ThMonoid, ThGroup,
        ThNat, ThNatPlus, ThNatPlusTimes

using ...Dsl
using ...Syntax: ThEmpty

# Category theory
@theory ThSet <: ThEmpty begin
  Ob::TYPE ⊣ []
end

@theory ThGraph <: ThSet begin
  Hom(dom,codom)::TYPE ⊣ [dom::Ob, codom::Ob]
end

@theory ThLawlessCat <: ThGraph begin
  (f ⋅ g)::Hom(a,c) ⊣ [a::Ob, b::Ob, c::Ob, f::Hom(a,b), g::Hom(b,c)]
end

@theory ThAscCat <: ThLawlessCat begin
  assoc := ((f ⋅ g) ⋅ h) == (f ⋅ (g ⋅ h)) :: Hom(a,d) ⊣ [a::Ob, b::Ob, c::Ob, d::Ob, f::Hom(a,b), g::Hom(b,c), h::Hom(c,d)]
end

@theory ThIdLawlessCat <: ThAscCat begin
  id(a)::Hom(a,a) ⊣ [a::Ob]
end

@theory ThCategory <: ThIdLawlessCat begin
  idl := id(a) ⋅ f == f :: Hom(a,b) ⊣ [a::Ob, b::Ob, f::Hom(a,b)]
  idr := f ⋅ id(b) == f :: Hom(a,b) ⊣ [a::Ob, b::Ob, f::Hom(a,b)]
end

@theory ThThinCategory <: ThCategory begin
  thineq := f == g :: Hom(A,B) ⊣ [A::Ob, B::Ob, f::Hom(A,B), g::Hom(A,B)]
end

@theory ThPreorder <: ThSet begin
  Leq(a,b)::TYPE ⊣ [a::Ob, b::Ob]

  # Preorder axioms are lifted to term constructors in the GAT.
  refl(A)::Leq(A,A) ⊣ [A::Ob] # ∀ A there is a term reflexive(A) which implies Leq A,A
  trans(f, g)::Leq(A,C) ⊣ [A::Ob, B::Ob, C::Ob, f::Leq(A,B),g::Leq(B,C)]

  # Axioms of the GAT are equivalences on terms or simplification rules in the logic
  thineq := f == g :: Leq(A,B) ⊣ [A::Ob, B::Ob, f::Leq(A,B), g::Leq(A,B)]
end

"""
Defining ThMonotoneMap via pushout (+ morphisms MMdom and MMcodom)

@theory ThMonotoneMap
  MMdom <: ThPreorder{
    Ob = Ob1
    Leq = Leq1
    refl = refl1
    trans = trans1
  }
  MMcodom <: ThPreorder{
    Ob = Ob2
    Leq = Leq2
    refl = refl2
    trans = trans2
  }

  f(a) :: Ob2  ⊣ [(a::Ob1,)]
  mono(lt) :: Leq2(f(x),f(y))) ⊣ [(x::Ob1, y::Ob1), (lt::Leq(x,y),)]
end
"""


# Abstract algebra
@theory ThMagma <: ThSet begin
  (x ∘ y)::Ob ⊣ [x::Ob, y::Ob]
end

@theory ThSemiGroup <: ThMagma begin
  ((x ∘ y) ∘ z == (x ∘ (y ∘ z)) :: Ob) ⊣ [x::Ob, y::Ob, z::Ob]
end

@theory ThMonoid <: ThSemiGroup begin
  e() :: Ob ⊣ []
  (e() ∘ x == x :: Ob) ⊣ [x::Ob]
  (x ∘ e() == x :: Ob) ⊣ [x::Ob]
end

@theory ThGroup <: ThMonoid begin
  i(x) :: Ob ⊣ [x::Ob]
  (i(x) ∘ x == e :: Ob) ⊣ [x::Ob]
  (x ∘ i(x) == e :: Ob) ⊣ [x::Ob]
end

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
