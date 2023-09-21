module Arithmetic 

export IntNatPlus

using ....Models
using ...StdTheories

struct IntNatPlus <: Model{Tuple{Int}} end

@instance ThNatPlus{Int} [model::IntNatPlus] begin
  Z() = 0
  S(n::Int) = n + 1
  +(x::Int, y::Int) = x + y
end

end # module 
