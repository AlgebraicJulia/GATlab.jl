module ModelTests

using Test
using Gatlab

using StructEquality

@struct_hash_equal struct FinSet
  n::Int
end

@struct_hash_equal struct FinFunction
  dom::FinSet
  codom::FinSet
  values::Vector{Int}
end

module FinSetImpl
using ..ModelTests: FinSet, FinFunction

check(::FinSet) = true
check(f::FinFunction) = length(f.values) == f.dom.n && all(f.values[x] ∈ 1:f.codom.n for x in 1:f.dom.n)

dom(f::FinFunction) = f.dom
codom(f::FinFunction) = f.codom

(f ⋅ g) = FinFunction(dom(f), codom(g), [g.values[f.values[x]] for x in 1:dom(f).n])
id(a::FinSet) = FinFunction(a, a, collect(1:a.n))
end

@simple_model ThCategory FinSetC FinSetImpl

a = FinSet(2)
f = FinFunction(a,a,[1,2])

@test ap(FinSetC(), Val(5), a) == f
@test typarg(FinSetC(), Val(2), Val(1), f) == a

end
