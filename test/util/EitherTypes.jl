module TestEitherTypes

using GATlab
using Test

@test convert(Right{Any}, Right(:a)) == Right{Any}(:a)

xs = Either{Number, Any}[]
push!(xs, Right(:a))
push!(xs, Left(1))
@test xs == [Right(:a), Left(1)]

end
