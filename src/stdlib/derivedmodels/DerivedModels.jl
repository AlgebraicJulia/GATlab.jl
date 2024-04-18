module DerivedModels
# export OpFinSetC, IntMonoid, IntPreorderCat

using ....Models
using ...StdTheoryMaps
using ...StdModels

# Given a model of a category C, we can derive a model of Cᵒᵖ.
# @migrate OpFinSetC = OpCat(FinSetC)

# Interpret `e` as `0` and `⋅` as `+`.
# @migrate IntMonoid = NatPlusMonoid(IntNatPlus)

# Interpret `id` as reflexivity and `compose` as transitivity.
# @migrate IntPreorderCat = PreorderCat(IntPreorder)

end
