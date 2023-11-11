module DerivedModels
export OpFinSetC, IntMonoid, IntPreorderCat

using ....Models
using ...StdTheoryMaps
using ...StdModels

# Given a model of a category C, we can derive a model of Cᵒᵖ.
OpFinSetC = migrate_theory(OpCat, FinSetC())

# Interpret `e` as `0` and `⋅` as `+`.
IntMonoid = migrate_theory(NatPlusMonoid, IntNatPlus())

# Interpret `id` as reflexivity and `compose` as transitivity.
IntPreorderCat = migrate_theory(PreorderCat, IntPreorder())

end # module
