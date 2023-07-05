module TestSliceCategories

using Gatlab, Test

const C = SliceC{Int, Vector{Int}, FinSetC}(FinSetC(), 4)
const Ob = SliceOb{Int, Vector{Int}}

@test checkvalidity(C, ThCategory.Ob, Ob(3, [1,3,2]))
@test !checkvalidity(C, ThCategory.Ob, Ob(3, [1,3,2,4]))
@test !checkvalidity(C, ThCategory.Ob, Ob(3, [1,3,9]))
@test checkvalidity(C, ThCategory.Hom, Ob(3, [1,3,3]), Ob(2, [1,3]), [1,2,2])

end
