module TestSumTypes

using MLStyle
using GATlab.Util.SumTypes
using Test

@sum AlgebraExpr{T} begin
  Const(x::T)
  Sum(summands::Vector{Self})
  Product(factors::Vector{Self})
end

@test typeof(Const{Int}(2)) == AlgebraExpr{Int}

sum_type = sprint(show, Sum)
const_type = sprint(show, Const)
expr_type = sprint(show, AlgebraExpr)

@test sprint(show, (Sum{Int}([Const{Int}(3)]))) ==
      "$sum_type($expr_type{Int64}[$const_type(3)::$expr_type{Int64}])::$expr_type{Int64}"

@sum MonoidExpr begin
  Zero()
  Plus(t1::Self, t2::Self)
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
