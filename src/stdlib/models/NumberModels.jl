module NumberModels
export RealModel, AThRealAlg

using ....Syntax
using ....Models
using ....Dsl
using ...StdTheories

@model ThElementary{Real} (self::RealModel) begin
  default(::Real) = true

  zero() = 0

  one() = 1

  -(x) = -x

  +(x,y) = x + y

  *(x,y) = x * y

  sin(x) = sin(x)

  cos(x) = cos(x)

  tan(x) = tan(x)

  exp(x) = exp(x)

  sigmoid(x) = 1 / (1 + exp(-x))
end

struct AThRealAlg <: AugmentedTheory{ThElementary.T, RealModel}
end

Models.interp_val(::AThRealAlg, x::Real) = Const(ATyp(Lvl(1)), x)

end
