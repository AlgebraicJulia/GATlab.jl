module TestFinSets

using GATlab, Test

using .ThCategory

@withmodel FinSetC() (Ob, Hom, id, compose, dom, codom) begin
  @test Ob(0) == 0
  @test_throws TypeCheckFail Ob(-1)
  @test_throws TypeCheckFail Hom([1,5,2], 3, 4)
  @test Hom(Int[], 0, 4) == Int[]

  @test id(2) == [1,2]
  @test compose([5], [1,1,1,3,2]) == [2]
  @test dom([5]) == 1
  @test codom([5]; context=(c=10,)) == 10
end

end
