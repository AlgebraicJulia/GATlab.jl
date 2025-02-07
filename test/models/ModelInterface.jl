module TestModelInterface 

using GATlab, GATlab.Stdlib, Test, StructEquality

@struct_hash_equal struct FinSetC′ end

# ThCategory models
###################

# Failures to create an instance 
#-------------------------------

# Error if we fail to implement methods
@test_throws ErrorException @eval @instance ThCategory{Int, Vector{Int}} [model::FinSetC′] begin
end

# Error: missing `id`
@test_throws ErrorException @eval @instance ThCategory{Int, Vector{Int}} [model::FinSetC′] begin
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]
  dom(f::Vector{Int}) = length(f)
end

# Error if we don't implement methods with args of of right type (`id`)
@test_throws ErrorException @eval @instance ThCategory{Int, Vector{Int}} [model::FinSetC′] begin
  id(f::Vector{Int}) = f
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]
  dom(f::Vector{Int}) = length(f)
end

# Actual instance
#----------------

@instance ThCategory{Int, Vector{Int}} [model::FinSetC′] begin
Ob(i::Int) = i 

  # check f is Hom: n -> m
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

  id(m::Int) = collect(1:m)
  compose(f::Vector{Int}, g::Vector{Int}) = g[f]

  dom(f::Vector{Int}) = length(f)
end

# Using the instance
#-------------------

using .ThCategory

@test Ob[FinSetC′()](-1) == -1
@test Hom[FinSetC′()]([1,2,3], 3, 3) == [1,2,3]
@test_throws ErrorException Hom[FinSetC′()]([1,2,3], 3, 2)

@test_throws ErrorException Hom[FinSetC′()]([1,2,3], 3, 2)
@test_throws ErrorException Hom[FinSetC′()]([1,2,3], 2, 3)
@test compose[FinSetC′()]([1,3,2], [1,3,2]) == [1,2,3]

@test id[FinSetC′()](2) == [1,2]

@test dom[FinSetC′()]([1,2,3]) == 3
@test_throws MethodError codom[FinSetC′()]([1,2,3])

@test implements(FinSetC′(), ThCategory, [Int,Vector{Int}])
@test !implements(FinSetC′(), ThNatPlus, [Int])

# Monoidal category models 
##########################

# Failures to create an instance 
#-------------------------------

# Missing `mcompose` on objects (`Int`s)
@test_throws ErrorException @eval @instance ThStrictMonCat{Int, Vector{Int}} [model::FinSetC′] begin

  mcompose(f::Vector{Int}, g::Vector{Int}; context) = [f; g .+ context.B₁]

  munit() = 0
end


@test_throws ErrorException @eval @instance ThStrictMonCat{Int, Int} [model::FinSetC′] begin
  mcompose(a::Int, b::Int) = a + b
  mcompose(f::Int, g::Int; context) = f * g

  munit() = 0
end

# Actual instance
#----------------

@instance ThStrictMonCat{Int, Vector{Int}} [model::FinSetC′] begin

  mcompose(a::Int, b::Int) = a + b
  mcompose(f::Vector{Int}, g::Vector{Int}; context) = [f; g .+ context.B₁]

  munit() = 0
end

@test implements(FinSetC′(), ThStrictMonCat, [Int, Vector{Int}])

# Using the instance
#-------------------

using .ThStrictMonCat

@test mcompose[FinSetC′()](id[FinSetC′()](2), id[FinSetC′()](2); context=(;B₁=2)) ==
  id[FinSetC′()](4)

# Default (old-style) instance
#-----------------------------

@struct_hash_equal struct FinSet 
  n::Int 
end

@struct_hash_equal struct FinFunction 
  values::Vector{Int}
  dom::FinSet 
  codom::FinSet
  function FinFunction(values::AbstractVector, dom::FinSet, codom::FinSet)
    new(ThCategory.Hom[FinSetC′()](Vector{Int}(values), dom.n, codom.n), dom, codom)
  end
end 

@instance ThCategory{FinSet, FinFunction} begin
  Ob(x::FinSet) = x.n ≥ 0 ? x : error("expected nonnegative integer")

  function Hom(f::FinFunction, x::FinSet, y::FinSet)
    dom(f) == x || error("domain mismatch")
    codom(f) == y || error("codomain mismatch")
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
@test_throws ErrorException Hom(f, A, A)

@withmodel FinSetC′() (mcompose, id) begin
  @test mcompose(id(2), id(2); context=(;B₁=2)) == id(4)
end

@test_throws MethodError id(2)



# Test scenario where we extend a method
############################################################

# Note we no longer need to explicitly @import 

@theory T1 begin 
  X::TYPE; 
  h(a::X)::X 
end

@theory T2<:T1 begin 
  Y::TYPE; 
  h(b::Y)::Y 
end

@instance T1{Int} begin 
  h(a::Int) = 1 
end

@instance T2{Int,Bool} begin 
  h(b::Bool) = false 
end

@test h(2) == 1

@test h(false) == false

# Test models with abstract types 
#################################
 
""" Assume this implements Base.iterate """
abstract type MyAbsIter{V} end

struct MyVect{V} <: MyAbsIter{V}
  v::Vector{V}
end

Base.iterate(m::MyVect, i...) = iterate(m.v, i...)

@instance ThSet{V} [model::MyAbsIter{V}] where V begin 
  default(v::V) = v ∈ model ? v : error("Bad $v not in $model")
end

@test implements(MyVect([1,2,3]), ThSet, [Vector{Int}])

# this will fail unless WithModel accepts subtypes
@test ThSet.default[MyVect([1,2,3])](1) == 1

 
# Test wrapper structs
######################
"""Cat"""
ThCategory.Meta.@wrapper Cat Any

c = Cat(FinSetC′());
c2 = Cat(FinMatC{Int}());
@test_throws ErrorException Cat(MyVect([1,2,3])) # can't construct

@test getvalue(c) == FinSetC′()
@test impl_type(c, :Ob) == Int == impl_type(c2, :Ob)

@test Ob(c, 2) == 2
@test_throws MethodError Hom(c2, [1,2])

function id2(c::Cat)
  ThCategory.id(c, 2)
end

@test id2(c) == [1,2]
@test id2(c2) == [1 0; 0 1]
@test_throws MethodError id2(FinSetC′())

abstract type MyAbsType end
ThCategory.Meta.@wrapper Cat2 <: MyAbsType 
@test Cat2 <: MyAbsType

# Typed wrappers
#----------------
"""Typed Cat"""
ThCategory.Meta.@typed_wrapper TCat

c = TCat(FinSetC′())
@test c == TCat{Int,Vector{Int}}(FinSetC′())
@test_throws ErrorException TCat{Bool,Symbol}(FinSetC′()) # Ob: Int ⊄ Bool
@test c isa TCat{Int, Vector{Int}}
@test id(c, 2) == [1,2]

c2 = TCat(FinMatC{Int}());
@test c2 isa TCat{Int, Matrix{Int}}

@test id(c2, 2) == [1 0; 0 1]

# Empty tuples
#----------------
@instance ThCategory{Union{}, Union{}} [model::Nothing] begin
  id(x::Union{}) = x
  compose(f::Union{},g::Union{}) = f
end

@test TCat(nothing) isa TCat{Union{},Union{}}

# Test implements 
#################
T = ThCategory.Meta.theory
(_, c), (_, i) = termcons(T)

implements(FinSetC′(), ThCategory, :id) # no arg type checking, just method + arity checking

@test implements(FinSetC′(), ThCategory, :id, [Int])
@test !implements(FinSetC′(), ThCategory, :id, [String])
@test !implements(FinSetC′(), ThCategory, :id, [Any]) # is this bad?

# there is a compose(::Vect,::Vect)
@test implements(FinSetC′(), ThCategory, c, [Int, Vector{Int}]) 

# no id(::String)
@test !implements(FinSetC′(), ThCategory, i, [String, Vector{Int}]) 

@test implements(FinSetC′(), ThCategory, [Int, Vector{Int}]) 
@test !implements(FinSetC′(), ThCategory, [String, Vector{Int}]) 

m = FinMatC{Float64}()

@test implements(m, ThCategory, i, [Int, Matrix{Int}])
@test implements(m, ThCategory, :id, [Int])
@test !implements(m, ThCategory, :id, [String])


struct Foo end
@instance ThCategory{Union{Symbol,String}, Int} [model::Foo] begin 
  compose(::Int,::Int) = 1
  id(s::Symbol) = 2 
  id(s::String) = 3
  id(::Union{Symbol, String})= error("Unreachable")
end

@test implements(Foo(), ThCategory, [Union{Symbol,String}, Int])
@test implements(Foo(), ThCategory, [String, Int])
@test !implements(Foo(), ThCategory, [String, String])

id[Foo()](:x) == 2
id[Foo()]("x") == 3

end # module
