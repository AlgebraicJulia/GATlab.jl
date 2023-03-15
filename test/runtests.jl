using Test

@testset "util" begin
  include("util/tests.jl")
end

@testset "syntax" begin
  include("syntax/tests.jl")
end

@testset "logic" begin
  include("logic/tests.jl")
end

@testset "theories" begin
  include("theories/tests.jl")
end
