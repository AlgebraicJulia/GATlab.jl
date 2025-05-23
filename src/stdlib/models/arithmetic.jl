export IntNat, IntNatPlus, IntPreorder, ZRing, BoolRing

using ...Models
using ..StdTheories

struct IntNat end

@instance ThNat{Int} [model::IntNat] begin
  Z() = 0
  S(n::Int) = n + 1
end

struct IntNatPlus end

@instance ThNatPlus{Int} [model::IntNatPlus] begin
  Z() = 0
  S(n::Int) = n + 1
  +(x::Int, y::Int) = x + y
end

struct IntPreorder end

@instance ThPreorder{Int, Tuple{Int,Int}} [model::IntPreorder] begin
  Leq(ab::Tuple{Int,Int}, a::Int, b::Int) = a ≤ b ? ab : error("$(ab[1]) ≰ $(ab[2])")
  refl(i::Int) = (i, i)
  trans(ab::Tuple{Int,Int}, bc::Tuple{Int,Int}) = if ab[2] == bc[1] 
    (ab[1], bc[2])
  else 
    error("Cannot compose $ab and $bc")
  end
end

struct ZRing end

@instance ThRing{Int} [model::ZRing] begin
  zero() = 0
  one() = 1
  -(x::Int) = -1 * x
  +(x::Int, y::Int) = x + y
  *(x::Int, y::Int) = x * y
end
