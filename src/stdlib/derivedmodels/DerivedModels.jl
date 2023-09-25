module DerivedModels
export OpFinSetC, IntMonoid, IntPreorderCat

using ....Models
using ...StdTheoryMaps
using ...StdModels

# Given a model of a category C, we can derive a model of Cᵒᵖ.
@migrate OpFinSetC = OpCat(FinSetC){Int, Vector{Int}}

# Interpret `e` as `0` and `⋅` as `+`.
@migrate IntMonoid = NatPlusMonoid(IntNatPlus){Int}

# Interpret `id` as reflexivity and `compose` as transitivity.
@migrate IntPreorderCat = PreorderCat(IntPreorder){Int, Tuple{Int,Int}}

end
