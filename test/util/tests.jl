module TestUtils

using Test

@testset "MetaUtils" begin
  include("MetaUtils.jl")
end

@testset "Either Type" begin
  include("EitherTypes.jl")
end

end
