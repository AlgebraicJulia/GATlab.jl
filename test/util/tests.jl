module TestUtils

using Test

@testset "MetaUtils" begin
  include("MetaUtils.jl")
end

@testset "Tries" begin
  include("Tries.jl")
end

end
