module TestSumTypes

using MLStyle
using GATlab.Util.SumTypes
using Test

# Unit tests of parsing

@test SumTypes.fromexpr(:(x<:Int), SumTypes.TypeArg) isa SumTypes.TypeArg
@test_throws ErrorException SumTypes.fromexpr(:(x::Int), SumTypes.TypeArg)

@test SumTypes.toexpr(SumTypes.fromexpr(:(x<:Int), SumTypes.TypeArg)) == :(x<:Int)

@test SumTypes.toexpr(SumTypes.fromexpr(:(X{Y}), SumTypes.BaseType)) == :(X{Y})
@test_throws ErrorException SumTypes.fromexpr(:(1+1), SumTypes.BaseType)

@test SumTypes.fromexpr(:(x::Int), SumTypes.Field) isa SumTypes.Field
@test_throws ErrorException SumTypes.fromexpr(:(1+1), SumTypes.Field)

@test SumTypes.fromexpr(:(V(x::Int)), SumTypes.Variant) isa SumTypes.Variant
@test_throws ErrorException SumTypes.fromexpr(:(V{}), SumTypes.Variant)

# Integration tests

@sum AlgebraExpr{T} begin
  Const(x::T)
  Sum(summands::Vector{AlgebraExpr{T}})
  Product(factors::Vector{AlgebraExpr{T}})
end

@test typeof(Const{Int}(2)) == AlgebraExpr{Int}

sum_type = sprint(show, Sum)
const_type = sprint(show, Const)
expr_type = sprint(show, AlgebraExpr)

@test sprint(show, (Sum{Int}([Const{Int}(3)]))) ==
      "$sum_type($expr_type{Int64}[$const_type(3)::$expr_type{Int64}])::$expr_type{Int64}"

@sum MonoidExpr begin
  Zero()
  Plus(t1::MonoidExpr, t2::MonoidExpr)
end

res = @match Plus(Zero(), Zero()) begin
  Zero() => 0
  Plus(t1, t2) => (t1, t2)
end

@test res == (Zero(), Zero())

res = @match Zero() begin
  Zero() => 0
  Plus(t1, t2) => (t1, t2)
end

@test res == 0

end
