@model ThElementary{Num} (self::NumR) begin
  default(::Num) = true

  zero() = 0

  one() = 1

  -(x) = Base.:(-)(x)

  +(x,y) = Base.:(+)(x,y)

  *(x,y) = Base.:(*)(x,y)

  sin(x) = Base.sin(x)

  cos(x) = Base.cos(x)

  tan(x) = Base.tan(x)

  exp(x) = Base.exp(x)

  sigmoid(x) = 1 / (1 + exp(-x))
end
