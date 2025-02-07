module TestNothings

using Test, GATlab, GATlab.Stdlib

using .ThCategory

@withmodel NothingC() (Ob, Hom, dom, codom, compose, id) begin
  @test Ob(nothing) == nothing
  @test Hom(nothing, nothing, nothing) == nothing
  @test isnothing(dom(nothing))
  @test isnothing(codom(nothing))
  @test isnothing(id(nothing))
  @test isnothing(compose(nothing, nothing))
end

end # module
