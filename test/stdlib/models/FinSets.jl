module TestFinSets

using Gatlab, Test

@test checkvalidity(FinSetC(), ThCategory.Ob(), 0)
@test !checkvalidity(FinSetC(), ThCategory.Ob(), -1)
@test !checkvalidity(FinSetC(), ThCategory.Hom(), 3, 4, [1,5,2])
@test checkvalidity(FinSetC(), ThCategory.Hom(), 0, 4, Int[])

@test ap(FinSetC(), ThCategory.id(), 2) == collect(1:2)
@test ap(FinSetC(), ThCategory.compose(), 1, 5, 3, [5], [1,1,1,3,2]) == [2]

@test checkvalidity(TypedFinSetC(3), ThCategory.Ob(), [1,2,1])
@test !checkvalidity(TypedFinSetC(2), ThCategory.Ob(), [3,3])

end
