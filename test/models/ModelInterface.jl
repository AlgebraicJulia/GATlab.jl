module TestModelInterface 

using Gatlab
using Test
using StructEquality

struct FinSetC <: Model{Tuple{Int, Vector{Int}}}
end

@instance ThCategory{Int, Vector{Int}} (;model::FinSetC) begin
  Hom(f::Vector{Int}, n::Int, m::Int) = # check f is Hom: n -> m
     length(f) == n && all(1 <= y <= m for y in f) 

  id(m::Int) = collect(1:m)
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]

  dom(f::Vector{Int}) = length(f)
end

@test ThCategory.Ob(-1; model=FinSetC()) # Yikes!
@test ThCategory.Hom([1,2,3], 3, 3; model=FinSetC())
@test !ThCategory.Hom([1,2,3], 3, 2; model=FinSetC())
@test !ThCategory.Hom([1,2,3], 2, 3; model=FinSetC())
@test ThCategory.compose([1,3,2], [1,3,2]; model=FinSetC()) == [1,2,3]

@test ThCategory.id(2; model=FinSetC()) == [1,2]

@test ThCategory.dom([1,2,3]; model=FinSetC()) == 3
@test_throws ErrorException ThCategory.codom([1,2,3]; model=FinSetC())

@test implements(FinSetC(), ThCategory)

# Todo: get things working where Ob and Hom are the same type (i.e. binding dict not monic)
struct TypedFinSetC <: Model{Tuple{Vector{Int}, Vector{Int}}}
  ntypes::Int
end

@instance ThStrictMonCat{Int, Vector{Int}} (;model::FinSetC) begin
  @import Ob, Hom, id, compose, dom, codom

  mcompose(a::Int, b::Int) = a + b
  mcompose(f::Vector{Int}, g::Vector{Int}; context) = [f; g .+ context.B₁]

  munit() = 0
end

@test implements(FinSetC(), ThStrictMonCat)

using .ThStrictMonCat

@test mcompose(id(2; model=FinSetC()), id(2; model=FinSetC()); context=(;B₁=2), model=FinSetC()) ==
  id(4; model=FinSetC())

@struct_hash_equal struct FinSet 
  n::Int 
end

@struct_hash_equal struct FinFunction 
  values::Vector{Int}
  dom::FinSet 
  codom::FinSet 
end 

@instance ThCategory{FinSet,FinFunction} begin 
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

@withmodel FinSetC() (mcompose, id) begin
  @test mcompose(id(2), id(2); context=(;B₁=2)) == id(4)
end

@test_throws UndefKeywordError id(2) # the macro does not globally overload methods

@test_throws LoadError @eval @instance ThCategory{Int, Vector{Int}} (;model::FinSetC) begin
end

@test_throws LoadError @eval @instance ThCategory{Int, Vector{Int}} (;model::FinSetC) begin
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]
  dom(f::Vector{Int}) = length(f)
end

@test_throws LoadError @eval @instance ThCategory{Int, Vector{Int}} (;model::FinSetC) begin
  id(f::Vector{Int}) = f
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]
  dom(f::Vector{Int}) = length(f)
end


@test_throws LoadError @eval @instance ThStrictMonCat{Int, Vector{Int}} (;model::FinSetC) begin
  @import Ob, Hom, id, compose, dom, codom

  mcompose(f::Vector{Int}, g::Vector{Int}; context) = [f; g .+ context.B₁]

  munit() = 0
end

@test_throws LoadError @eval @instance ThStrictMonCat{Int, Int} (;model::FinSetC) begin
  @import Ob, Hom, id, compose, dom, codom

  mcompose(a::Int, b::Int) = a + b
  mcompose(f::Int, g::Int; context) = f * g

  munit() = 0
end

end # module
