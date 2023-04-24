module DslTests

using Test
using Gatlab

ctx = @context ThRing [a, :d(a)]

@test ctx.ctx[2][1] == Name(:a; annotation=:d)

end
