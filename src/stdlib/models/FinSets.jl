module FinSets
export FinSetC

using ....Models
using ...StdTheories

struct FinSetC <: Model{Tuple{Int, Vector{Int}}}
end

@instance ThCategory{Int, Vector{Int}} (;model::FinSetC) begin
  Ob(x::Int) = x >= 0 ? x : @fail "expected nonnegative integer"

  function Hom(f::Vector{Int}, n::Int, m::Int)
    if length(f) == n
      for i in 1:n
        if f[i] ∉ 1:m
          @fail "index not in codomain: $i"
        end
      end
      f
    else
      @fail "length of morphism does not match domain: $(length(f)) != $m"
    end
  end

  id(x::Int) = collect(1:x)
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]

  dom(f::Vector{Int}) = length(f)
end

end
