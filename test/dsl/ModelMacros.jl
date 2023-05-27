module TestModelMacros

using Gatlab, Test

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

@test ap(IntArith(), ThRig.zero()) == 0
@test ap(IntArith(), ThRig.:(+)(), 4, 5) == 9
@test ap(IntMaxPlus(), ThRig.one()) == 0
@test ap(IntMaxPlus(), ThRig.:(+)(), 4, 5) == 5

end
