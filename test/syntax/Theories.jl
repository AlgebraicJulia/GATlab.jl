module Theories

using Gatlab
using Test

th_category = gettheory(ThCategory.T)

arg_exprs = derive_context_from_args(th_category, th_category[getlevel(ThCategory.compose)])

@test arg_exprs[1] == ArgExpr[
  IndirectArg(getlevel(ThCategory.Hom), 1, DirectArg(1))
]
@test arg_exprs[2] == ArgExpr[
  IndirectArg(getlevel(ThCategory.Hom), 1, DirectArg(2)),
  IndirectArg(getlevel(ThCategory.Hom), 2, DirectArg(1)),
]
@test arg_exprs[3] == ArgExpr[
  IndirectArg(getlevel(ThCategory.Hom), 2, DirectArg(2))
]

@test arg_exprs[4] == ArgExpr[DirectArg(1)]
@test arg_exprs[5] == ArgExpr[DirectArg(2)]

end
