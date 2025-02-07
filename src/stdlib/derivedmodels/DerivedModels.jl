module DerivedModels
export OpFinSetC, IntMonoid, IntPreorderCat

using ....Models
using ...StdTheoryMaps
using ...StdModels

# Given a model of a category C, we can derive a model of Cᵒᵖ.
OpFinSetC = migrate_model(OpCat, FinSetC(), :OpFinSetCat)

# Interpret `e` as `0` and `⋅` as `+`.
IntMonoid = migrate_model(NatPlusMonoid, IntNatPlus())

# Interpret `id` as reflexivity and `compose` as transitivity.
IntPreorderCat = migrate_model(PreorderCat, IntPreorder())

end # module
