using Test 


@testset "Parse" begin
  include("Parse.jl")
end

@testset "Visualization" begin
  include("Visualization.jl")
end

@testset "GATs" begin
  include("GATs.jl")
end
