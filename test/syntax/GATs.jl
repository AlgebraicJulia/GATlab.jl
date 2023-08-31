module TestGATs 

using Gatlab, Test

compose_constructor = getvalue(ThCategory.THEORY[ThCategory.THEORY.termcons[1]])

@test length(equations(compose_constructor.args, compose_constructor.localcontext, ThCategory.THEORY))==5

end # module 