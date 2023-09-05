module TestFinSets

using Gatlab, Test

using .ThCategory

@withmodel FinSetC() (Ob, Hom, id, compose, dom) begin
  @test Ob(0)
  @test !Ob(-1)
  @test !Hom([1,5,2], 3, 4)
  @test Hom(Int[], 0, 4)

  @test id(2) == [1,2]
  @test compose([5], [1,1,1,3,2]) == [2]
  @test dom([5]) == 1
end

end
