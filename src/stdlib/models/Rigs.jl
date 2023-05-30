module Rigs
export IntArith, IntMaxPlus

using ....Models
using ....Dsl
using ...StdTheories

@model ThRig{Int} (self::IntArith) begin
  default(x::Int) = true
  zero() = 0
  one() = 1
  (x + y) = Base.:(+)(x,y)
  (x * y) = Base.:(*)(x,y)
end

@model ThRig{Int} (self::IntMaxPlus) begin
  default(x::Int) = true
  zero() = typemin(Int)
  one() = 0
  (x + y) = max(x,y)
  (x * y) = Base.:(+)(x,y)
end

end
