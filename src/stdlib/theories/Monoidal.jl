module Monoidal
export ThLawlessMonCat, ThStrictMonCat

using ..Categories
using ....Syntax

@theory ThLawlessMonCat <: ThCategory begin
  mcompose(A::Ob, B::Ob) :: Ob
  munit() :: Ob
  mcompose(f₁::(A₁ → B₁), f₂::(A₂ → B₂)) :: Hom(mcompose(A₁,A₂), mcompose(B₁, B₂)) ⊣ [(A₁, A₂, B₁, B₂)::Ob]
  @op begin
    I := munit
    (⊗) := mcompose
  end
end

@theory ThStrictMonCat <: ThLawlessMonCat begin
  (A ⊗ B) ⊗ C == (A ⊗ (B ⊗ C)) :: Ob ⊣ [(A,B,C)::Ob]
  I ⊗ A == A :: Ob ⊣ [A::Ob]
  A ⊗ I == A :: Ob ⊣ [A::Ob]
end

end
