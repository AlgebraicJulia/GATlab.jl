export ZMatricesOne

using ...Models
using ..StdTheories

struct ZMatricesOne <: Model{Tuple{Int}} end

# TODO I'd like to improve the error for julia signature. If I don't provide the second Int, KeyError: key AlgSort(R, #2) not found is returned.
# TODO include other models...?
@instance ThMod{Int,Int} [model::ZMatricesOne] begin
  # Ab
  e() = 0
  i(A::Int) = -1 * A
  ⊕(A::Int, B::Int) = A + B
  # Ring
  zero() = 0
  unit() = 1
  *(a::Int, b::Int) = a * b
  +(a::Int, b::Int) = a + b
  -(a::Int) = -1 * a 
  # Module
  ⋅(r::Int, A::Int) = r * A
end

using .ThMod
import .ThMod: zero, one, -, +, *, unit

@withmodel ZMatricesOne() (e, i, ⊕, zero, unit, *, +, -, ⋅) begin
    (2⋅3) ⊕ 5
end

struct ZMatricesTwo <: Model{Tuple{Int}} end

@instance ThMod{Array{Int,2},Int} [model::ZMatricesTwo] begin
  # Ab
  e() = zeros(2,1)
  i(A::Array{Int, 2}) = -1 * A
  ⊕(A::Array{Int, 2}, B::Array{Int, 2}) = A + B
  # Ring
  zero() = 0
  unit() = 1
  *(a::Int, b::Int) = a * b
  +(a::Int, b::Int) = a + b
  -(a::Int) = -1 * a
  # Module
  ⋅(r::Int, A::Array{Int, 2}) = r * A
end

@withmodel ZMatricesTwo() (e, i, ⊕, zero, unit, *, +, -, ⋅) begin
    (2⋅[1 2
        3 4]) ⊕ [1 2
                 3 4]
end

struct RMatricesTwo <: Model{Tuple{Int}} end

@instance ThMod{Array{Float64,2},Int} [model::RMatricesTwo] begin
  # Ab
  e() = zeros(2,1)
  i(A::Array{Float64, 2}) = -1 * A
  ⊕(A::Array{Float64, 2}, B::Array{Float64, 2}) = A + B
  # Ring
  zero() = 0
  unit() = 1
  *(a::Int, b::Int) = a * b
  +(a::Int, b::Int) = a + b
  -(a::Int) = -1 * a
  # Module
  ⋅(r::Int, A::Array{Float64, 2}) = r * A
end

@withmodel RMatricesTwo() (e, i, ⊕, zero, unit, *, +, -, ⋅) begin
    i(2⋅rand(2,2) ⊕ rand(2,2))
end
