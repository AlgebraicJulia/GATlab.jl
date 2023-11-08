module DerivedModels
export OpFinSetC, IntMonoid, IntPreorderCat

using ....Models
using ...StdTheoryMaps
using ...StdModels

# Given a model of a category C, we can derive a model of Cᵒᵖ.
@migrate_model OpFinSetC = OpCat(FinSetC)

# Interpret `e` as `0` and `⋅` as `+`.
@migrate_model IntMonoid = NatPlusMonoid(IntNatPlus)

# Interpret `id` as reflexivity and `compose` as transitivity.
@migrate_model IntPreorderCat = PreorderCat(IntPreorder)

end
