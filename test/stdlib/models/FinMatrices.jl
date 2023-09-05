module TestFinMatrices

using Gatlab, Test

using .ThCategory

@withmodel FinMatC{Float64}() (Ob, Hom, id, compose) begin
  @test Ob(0)
  @test !Ob(-1)
  @test Hom([1. 0; -1 1], 2, 2)
  @test_throws MethodError Hom([1 0; 0 1], 2, 2)

  @test id(2) == [1. 0; 0 1]

  @test compose(id(2), id(2)) == id(2)
end

end
