module FinMatrices
export FinMatC, TypedFinSetC

using ....Models
using ....Dsl
using ...StdTheories

@model ThCategory{Int, Matrix{T}} (self::FinMatC{T<:Number}) begin
  Ob(n::Int) = n >= 0
  Hom(n::Int, m::Int, A::Matrix{T}) = size(A) == (n,m)

  id(n::Int) = T[T(i == j) for i in 1:n, j in 1:n]
  ⋅(_, _, _, A, B) = A * B
end

end
