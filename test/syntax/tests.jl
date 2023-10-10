module TestSyntax

using Test
using GATlab

@testset "Scopes" begin
  include("Scopes.jl")
end

@testset "ExprInterop" begin
  include("ExprInterop.jl")
end

@testset "GATs" begin
  include("GATs.jl")
end

@testset "GATContexts" begin
  include("GATContexts.jl")
end

@testset "TheoryInterface" begin
  include("TheoryInterface.jl")
end

@testset "TheoryMaps" begin
  include("TheoryMaps.jl")
end

@testset "EGraphs" begin
  include("EGraphs.jl")
end


end
