module FinSets

using ....Models
using ....Dsl
using ...StdTheories

@simple_model ThCategory FinSetC{Int, Vector{Int}} begin
  Ob(x::Int) = true
  Hom(x::Int, y::Int, f::Vector{Int}) = length(f) == x && all(j ∈ 1:y for j in f)

  id(x::Int) = collect(1:x)
  ⋅(x::Int, y::Int, z::Int, f::Vector{Int}, g::Vector{Int}) =
    Int[g[j] for j in f]
end

end
