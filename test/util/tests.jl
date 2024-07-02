module TestUtils

using Test

@testset "MetaUtils" begin
  include("MetaUtils.jl")
end

@testset "Dtrys" begin
  include("Dtrys.jl")
end

end
