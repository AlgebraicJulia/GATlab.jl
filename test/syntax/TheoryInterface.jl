module TestTheoryInterface

using Test, GATlab

@theory ThCategoryTypes begin
  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE
  @op (→) := Hom
end

@test ThCategoryTypes.Ob isa Function
@test ThCategoryTypes.Hom isa Function
@test Set(allnames(ThCategoryTypes.Meta.theory)) == Set([:Ob, :Hom, :dom, :codom])
@test Set(allnames(ThCategoryTypes.Meta.theory; aliases=true)) == Set([:Ob, :Hom, :(→), :dom, :codom])

using .ThCategoryTypes

@test dom isa Function
@test Hom != →
@test parentmodule(dom) == TestTheoryInterface

@theory ThLawlessCategory <: ThCategoryTypes begin
  compose(f::(a → b), g::Hom(b, c)) :: Hom(a, c) ⊣ [a::Ob, b::Ob, c::Ob]
  id(a::Ob)::Hom(a, a)
  @op (⋅) := compose
end

using .ThLawlessCategory

@test compose isa Function
@test compose != (⋅)
@test parentmodule(id) == TestTheoryInterface
@test Set(allnames(ThLawlessCategory.Meta.theory)) == Set([:Ob, :Hom, :dom, :codom, :compose, :id])
@test nameof(ThLawlessCategory.Meta.theory) == :ThLawlessCategory

@test_throws Exception @eval @theory ThDoubleCategory <: ThCategory begin
  Hom(dom::Ob, codom::Ob) :: TYPE
end

@test_throws Exception @eval @theory ThMonoid <: ThSemiGroup begin
  e() :: default
  e ⋅ x == x ⊣ [x]
end

@test_throws Exception @eval @theory ThBadAliases <: ThCategory begin
  @op 1 + 1
end

# test that a theory with redundant using statements is equal to one which hasn't
@theory ThMagmaMagmaWithAssoc begin
  using ThMagma
  using ThMagma
  (x ⋅ y) ⋅ z == (x ⋅ (y ⋅ z)) ⊣ [x, y, z]
end

end
