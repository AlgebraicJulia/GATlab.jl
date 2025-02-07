module TestFinMatrices

using GATlab, GATlab.Stdlib, Test

using .ThCategory

@withmodel FinMatC{Float64}() (Ob, Hom, id, compose, dom, codom) begin
  @test Ob(0) == 0
  @test_throws ErrorException Ob(-1)
  @test Hom([1. 0; -1 1], 2, 2) == [1. 0; -1 1]
  @test_throws ErrorException Hom([1. 0], 2, 2)
  @test_throws MethodError Hom([1 0; 0 1], 2, 2)

  @test id(2) == [1. 0; 0 1]

  @test compose(id(2), id(2)) == id(2)

  @test dom(id(2)) == 2
  @test codom(id(2)) == 2

end

# Test that `impl_type` is sensitive to the `where` parameters
@test impl_type(FinMatC{Float64}(), ThCategory, :Hom) == Matrix{Float64}

end # module
