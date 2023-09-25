module Arithmetic 

export IntNatPlus, IntPreorder

using ....Models
using ...StdTheories

struct IntNatPlus <: Model{Tuple{Int}} end

@instance ThNatPlus{Int} [model::IntNatPlus] begin
  Z() = 0
  S(n::Int) = n + 1
  +(x::Int, y::Int) = x + y
end

struct IntPreorder <: Model{Tuple{Int, Tuple{Int,Int}}} end

@instance ThPreorder{Int, Tuple{Int,Int}} [model::IntPreorder] begin
  Leq(ab::Tuple{Int,Int}, a::Int, b::Int) = a ≤ b ? ab : @fail "$(ab[1]) ≰ $(ab[2])"
  refl(i::Int) = (i, i)
  trans(ab::Tuple{Int,Int}, bc::Tuple{Int,Int}) = if ab[2] == bc[1] 
    (ab[1], bc[2])
  else 
    @fail "Cannot compose $ab and $bc"
  end
end


end # module 
