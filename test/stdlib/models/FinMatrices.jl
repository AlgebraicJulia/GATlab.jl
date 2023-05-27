module TestFinMatrices

using Gatlab, Test

@test typeof(ap(FinMatC{Int}(), ThCategory.id(), 2)) == Matrix{Int}
@test typeof(ap(FinMatC{Float64}(), ThCategory.id(), 2)) == Matrix{Float64}

end
