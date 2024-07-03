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
@test sprint(show, (Sum{Int}([Const{Int}(3)]))) ==
      "Sum(AlgebraExpr{Int64}[Const(3)::AlgebraExpr{Int64}])::AlgebraExpr{Int64}"

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
