module TestTheoryInterface

using Test, Gatlab

@theory ThCategoryTypes begin
  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE
  @op (→) := Hom
end

@test ThCategoryTypes.Ob isa Function
@test ThCategoryTypes.Hom isa Function
@test Set(allnames(ThCategoryTypes.THEORY)) == Set([:Ob, :Hom, :dom, :codom])

using .ThCategoryTypes

@test dom isa Function
@test Hom == →
@test parentmodule(dom) == ThCategoryTypes

@theory ThLawlessCategory <: ThCategoryTypes begin
  compose(f::(a → b), g::Hom(b, c)) :: Hom(a, c) ⊣ [a::Ob, b::Ob, c::Ob]
  id(a::Ob)::Hom(a, a)
  @op (⋅) := compose
end

using .ThLawlessCategory

@test compose isa Function
@test compose == (⋅)
@test parentmodule(id) == ThLawlessCategory
@test Set(allnames(ThLawlessCategory.THEORY)) == Set([:Ob, :Hom, :dom, :codom, :compose, :id])

end