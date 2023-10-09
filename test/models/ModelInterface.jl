module TestModelInterface 

using GATlab
using Test
using StructEquality

@struct_hash_equal struct FinSetC <: Model{Tuple{Int, Vector{Int}}}
end

@instance ThCategory{Int, Vector{Int}} [model::FinSetC] begin
  # check f is Hom: n -> m
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

  id(m::Int) = collect(1:m)
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]

  dom(f::Vector{Int}) = length(f)
end

using .ThCategory

@test Ob[FinSetC()](-1) == -1
@test Hom[FinSetC()]([1,2,3], 3, 3) == [1,2,3]
@test_throws TypeCheckFail Hom[FinSetC()]([1,2,3], 3, 2)

try
  ThCategory.Hom[FinSetC()]([1,2,3], 3, 2)
catch e
  @test e.model == FinSetC()
  @test e.theory == ThCategory.Meta.theory
  @test e.type == ident(ThCategory.Meta.theory; name=:Hom)
  @test e.val == [1, 2, 3]
  @test e.args == [3, 2]
  @test e.reason == "index not in codomain: 3"
  @test sprint(showerror, e) isa String
end

@test_throws TypeCheckFail Hom[FinSetC()]([1,2,3], 3, 2)
@test_throws TypeCheckFail Hom[FinSetC()]([1,2,3], 2, 3)
@test compose[FinSetC()]([1,3,2], [1,3,2]) == [1,2,3]

@test id[FinSetC()](2) == [1,2]

@test dom[FinSetC()]([1,2,3]) == 3
@test_throws ErrorException codom[FinSetC()]([1,2,3])

@test implements(FinSetC(), ThCategory)

# Todo: get things working where Ob and Hom are the same type (i.e. binding dict not monic)
struct TypedFinSetC <: Model{Tuple{Vector{Int}, Vector{Int}}}
  ntypes::Int
end

@instance ThStrictMonCat{Int, Vector{Int}} [model::FinSetC] begin
  @import Ob, Hom, id, compose, dom, codom

  mcompose(a::Int, b::Int) = a + b
  mcompose(f::Vector{Int}, g::Vector{Int}; context) = [f; g .+ context.B₁]

  munit() = 0
end

@test implements(FinSetC(), ThStrictMonCat)

using .ThStrictMonCat

@test mcompose[FinSetC()](id[FinSetC()](2), id[FinSetC()](2); context=(;B₁=2)) ==
  id[FinSetC()](4)

@struct_hash_equal struct FinSet 
  n::Int 
end

@struct_hash_equal struct FinFunction 
  values::Vector{Int}
  dom::FinSet 
  codom::FinSet
  function FinFunction(values::AbstractVector, dom::FinSet, codom::FinSet)
    new(ThCategory.Hom[FinSetC()](Vector{Int}(values), dom.n, codom.n), dom, codom)
  end
end 

@instance ThCategory{FinSet, FinFunction} begin
  Ob(x::FinSet) = x.n ≥ 0 ? x : @fail "expected nonnegative integer"

  function Hom(f::FinFunction, x::FinSet, y::FinSet)
    dom(f) == x || @fail "domain mismatch"
    codom(f) == y || @fail "codomain mismatch"
    f
  end

  # function Hom(values::Vector{Int}, dom::FinSet, codom::FinSet)
  #   FinFunction(values, dom, codom)
  # end

  dom(f::FinFunction) = f.dom 
  codom(f::FinFunction) = f.codom
  
  id(A::FinSet) = FinFunction(1:A.n, A, A)
  compose(f::FinFunction, g::FinFunction) = FinFunction(g.values[f.values], dom(f),codom(g))
end

A = FinSet(2)
B = FinSet(3)
f = FinFunction([2,3],A,B)
g = FinFunction([1,1,1],B,A)
@test id(A) == FinFunction([1,2], A, A)
@test compose(f,g) == FinFunction([1,1], A, A)
@test Hom(f, A, B) == f
# TODO:
# @test Hom([2,3], A, B) == f
@test_throws TypeCheckFail Hom(f, A, A)

@withmodel FinSetC() (mcompose, id) begin
  @test mcompose(id(2), id(2); context=(;B₁=2)) == id(4)
end

@test_throws MethodError id(2)

@test_throws LoadError @eval @instance ThCategory{Int, Vector{Int}} [model::FinSetC] begin
end

@test_throws LoadError @eval @instance ThCategory{Int, Vector{Int}} [model::FinSetC] begin
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]
  dom(f::Vector{Int}) = length(f)
end

@test_throws LoadError @eval @instance ThCategory{Int, Vector{Int}} [model::FinSetC] begin
  id(f::Vector{Int}) = f
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]
  dom(f::Vector{Int}) = length(f)
end

try
  @eval @instance ThCategory{Int, Vector{Int}} [model::FinSetC] begin
    id(f::Vector{Int}) = f
    compose(f::Vector{Int}, g::Vector{Int}) = g[f]
    dom(f::Vector{Int}) = length(f)
  end
catch e
  @test e.error isa SignatureMismatchError
  @test sprint(showerror, e.error) isa String
end

@test_throws LoadError @eval @instance ThStrictMonCat{Int, Vector{Int}} [model::FinSetC] begin
  @import Ob, Hom, id, compose, dom, codom

  mcompose(f::Vector{Int}, g::Vector{Int}; context) = [f; g .+ context.B₁]

  munit() = 0
end

@test_throws LoadError @eval @instance ThStrictMonCat{Int, Int} [model::FinSetC] begin
  @import Ob, Hom, id, compose, dom, codom

  mcompose(a::Int, b::Int) = a + b
  mcompose(f::Int, g::Int; context) = f * g

  munit() = 0
end

end # module
