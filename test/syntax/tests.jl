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

@testset "Presentations" begin
  include("Presentations.jl")
end

@testset "TheoryInterface" begin
  include("TheoryInterface.jl")
end

@testset "TheoryMaps" begin
  include("TheoryMaps.jl")
end


end
