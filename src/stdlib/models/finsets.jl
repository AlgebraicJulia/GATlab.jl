export FinSetC

using ...Models
using ..StdTheories

struct FinSetC end

@instance ThCategory{Int, Vector{Int}} [model::FinSetC] begin
  Ob(x::Int) = x >= 0 ? x : error("expected nonnegative integer")

  function Hom(f::Vector{Int}, n::Int, m::Int)
    if length(f) == n
      for i in 1:n
        if f[i] ∉ 1:m
          error("index not in codomain: $i")
        end
      end
      f
    else
      error("length of morphism does not match domain: $(length(f)) != $m")
    end
  end

  id(x::Int) = collect(1:x)
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]

  dom(f::Vector{Int}) = length(f)
  codom(::Vector{Int}; context) = context[:codom]
end
