module Preorders
export ThPreorder

using ....Dsl
using ....Syntax: ThEmpty
using ..Categories

@theory ThPreorder <: ThClass begin
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

end
