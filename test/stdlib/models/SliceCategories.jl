module TestSliceCategories

using Gatlab, Test

const C = SliceC{Int, Vector{Int}, FinSetC}(FinSetC(), 4)
const MkOb = SliceOb{Int, Vector{Int}}

using .ThCategory

@withmodel C (Ob, Hom, id, compose) begin
  @test Ob(MkOb(3, [1,3,2]))
  @test !Ob(MkOb(3, [1,3,2,4]))
  @test !Ob(MkOb(3, [1,3,9]))
  @test Hom([1,2,2], MkOb(3, [1,3,3]), MkOb(2, [1,3]))
end

end
