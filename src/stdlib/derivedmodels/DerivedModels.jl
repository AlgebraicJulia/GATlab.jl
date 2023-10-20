module DerivedModels
export OpFinSetC, IntMonoid, IntPreorderCat

using ....Models
using ...StdTheoryMaps
using ...StdModels

# Given a model of a category C, we can derive a model of Cᵒᵖ.
OpFinSetC = migrate(OpCat, FinSetC())

# Interpret `e` as `0` and `⋅` as `+`.
IntMonoid = migrate(NatPlusMonoid, IntNatPlus())

# Interpret `id` as reflexivity and `compose` as transitivity.
IntPreorderCat = migrate(PreorderCat, IntPreorder())

end # module
