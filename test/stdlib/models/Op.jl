"""Same as FinSetC tests but with all doms/codoms reversed"""
module TestOp

using GATlab, Test

using .ThCategory

@withmodel op(FinSetC()) (Ob, Hom, id, compose, dom, codom) begin
  @test Ob(0) == 0
  @test_throws TypeCheckFail Ob(-1)
  @test_throws TypeCheckFail Hom([1,5,2], 4, 3)
  @test Hom(Int[], 4, 0) == Int[]

  @test id(2) == [1,2]
  @test compose([1,1,1,3,2], [5]) == [2]
  @test compose([1,1,1,3,2], [5]; context=(;)) == [2]
  @test codom([5]) == 1
  @test dom([5]; context=(dom=10,)) == 10
end

end # module
