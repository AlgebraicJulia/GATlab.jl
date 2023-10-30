module DerivedModels
export OpFinSetC, IntMonoid, IntPreorderCat

using ....Models
using ...StdTheoryMaps
using ...StdModels

# Given a model of a category C, we can derive a model of Cᵒᵖ.
@migrate_theory OpFinSetC = OpCat(FinSetC)

# Interpret `e` as `0` and `⋅` as `+`.
@migrate_theory IntMonoid = NatPlusMonoid(IntNatPlus)

# Interpret `id` as reflexivity and `compose` as transitivity.
@migrate_theory IntPreorderCat = PreorderCat(IntPreorder)

end
