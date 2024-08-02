using Test

@testset "Signature" begin
  include("Signature.jl")
end

@testset "SSA Extraction" begin
  include("SSAExtract.jl")
end

@testset "Roe Utilities" begin
  include("Roe.jl")
end

@testset "ThDEC" begin
  include("ThDEC/tests.jl")
end
