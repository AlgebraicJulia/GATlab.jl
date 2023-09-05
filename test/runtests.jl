using Test

@testset "util" begin
  include("util/tests.jl")
end

@testset "syntax" begin
  include("syntax/tests.jl")
end

@testset "models" begin
  include("models/tests.jl")
end

@testset "stdlib" begin
  include("stdlib/tests.jl")
end
