module FinSets
export FinSetC

using ....Models
using ...StdTheories

struct FinSetC <: Model{Tuple{Int, Vector{Int}}}
end

@instance ThCategory{Int, Vector{Int}} (;model::FinSetC) begin
  Ob(x::Int) = x >= 0
  Hom(f::Vector{Int}, x::Int, y::Int) =
    length(f) == x && all(j ∈ 1:y for j in f)

  id(x::Int) = collect(1:x)
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]

  dom(f::Vector{Int}) = length(f)
end

end
