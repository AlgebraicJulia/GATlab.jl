module FinSets
export FinSetC, TypedFinSetC

using ....Models
using ....Dsl
using ...StdTheories

@model ThCategory{Int, Vector{Int}} (self::FinSetC) begin
  Ob(x::Int) = x >= 0
  Hom(x::Int, y::Int, f::Vector{Int}) = length(f) == x && all(j ∈ 1:y for j in f)

  id(x::Int) = collect(1:x)
  ⋅(x::Int, y::Int, z::Int, f::Vector{Int}, g::Vector{Int}) =
    Int[g[j] for j in f]
end

@model ThCategory{Vector{Int}, Vector{Int}} (self::TypedFinSetC) begin
  ntypes::Int

  Ob(v::Vector{Int}) = all(i ∈ 1:self.ntypes for i in v)
  Hom(x::Vector{Int}, y::Vector{Int}, f::Vector{Int}) = length(f) == length(x) &&
    all(1 <= j <= length(y) for j in f) &&
    all(x[i] == y[f[i]] for i in 1:length(x))

  id(v::Vector{Int}) = collect(1:length(v))
  ⋅(x, y, z, f::Vector{Int}, g::Vector{Int}) = Int[g[j] for j in f]
end

end
