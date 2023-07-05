module Monoidal
export ThLawlessMonCat, ThCoherencelessMonCat, ThStrictMonCat, mcompose

using ..Categories
using ....Dsl

@theory ThLawlessMonCat <: ThCategory begin
  (A ⊗ B) :: Ob ⊣ [(A,B)::Ob]
  (f₁ ⊗′ f₂) :: Hom(A₁ ⊗ A₂, B₁ ⊗ B₂) ⊣ [(A₁, A₂, B₁, B₂)::Ob, f₁::Hom(A₁, B₁), f₂::Hom(A₂, B₂)]
  I :: Ob
end

@theory ThCoherencelessMonCat <: ThLawlessMonCat begin
  assocr(A,B,C) :: Hom((A ⊗ B) ⊗ C, A ⊗ (B ⊗ C)) ⊣ [(A,B,C)::Ob]
  assocl(A,B,C) :: Hom(A ⊗ (B ⊗ C), (A ⊗ B) ⊗ C) ⊣ [(A,B,C)::Ob]
  assocr(A,B,C) ⋅ assocl(A,B,C) == id((A ⊗ B) ⊗ C) :: Hom((A ⊗ B) ⊗ C, (A ⊗ B) ⊗ C) ⊣ [(A,B,C)::Ob]
  assocl(A,B,C) ⋅ assocr(A,B,C) == id(A ⊗ (B ⊗ C)) :: Hom(A ⊗ (B ⊗ C), A ⊗ (B ⊗ C)) ⊣ [(A,B,C)::Ob]
  lunitf(A) :: Hom(A ⊗ I, A) ⊣ [A::Ob]
  lunitb(A) :: Hom(A, A ⊗ I) ⊣ [A::Ob]
  lunitf(A) ⋅ lunitb(A) == id(A ⊗ I) :: Hom(A ⊗ I, A ⊗ I) ⊣ [A::Ob]
  lunitb(A) ⋅ lunitf(A) == id(A) :: Hom(A, A) ⊣ [A::Ob]
  runitf(A) :: Hom(I ⊗ A, A) ⊣ [A::Ob]
  runitb(A) :: Hom(A, I ⊗ A) ⊣ [A::Ob]
  lunitf(A) ⋅ lunitb(A) == id(I ⊗ A) :: Hom(I ⊗ A, I ⊗ A) ⊣ [A::Ob]
  lunitb(A) ⋅ lunitf(A) == id(A) :: Hom(A,A) ⊣ [A::Ob]
end

@theory ThStrictMonCat <: ThLawlessMonCat begin
  (A ⊗ B) ⊗ C == (A ⊗ (B ⊗ C)) :: Ob ⊣ [(A,B,C)::Ob]
  I ⊗ A == A :: Ob ⊣ [A::Ob]
  A ⊗ I == A :: Ob ⊣ [A::Ob]
end

end
