module FinMatrices
export FinMatC

using ....Models
using ...StdTheories

struct FinMatC{T<:Number} <: Model{Tuple{T}}
end

@instance ThCategory{Int, Matrix{T}} (;model::FinMatC{T<:Number}) where {T} begin
  Ob(n::Int) = n >= 0
  Hom(A::Matrix{T}, n::Int, m::Int) = size(A) == (n,m)

  id(n::Int) = T[T(i == j) for i in 1:n, j in 1:n]
  compose(A::Matrix{T}, B::Matrix{T}) = A * B

  dom(A::Matrix{T}) = size(A)[1]
  codom(A::Matrix{T}) = size(A)[2]
end

end
