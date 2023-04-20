module MTKInterop

using ModelingToolkit

using ....Models
using ....Dsl
using ...StdTheories

using ..ContextMaps
using ..SimpleLenses

module Impl

zero() = 0

one() = 1

-(x) = Base.:(-)(x)

+(x,y) = Base.:(+)(x,y)

*(x,y) = Base.:(*)(x,y)

end

@simple_model ThRing NumR Impl

function ModelingToolkit.ODESystem(v::SimpleKleisliLens; name)
  length(v.codom.pos) == length(v.codom.dir) == 0 || error("Cannot integrate an open systems")
  length(v.dom.dir) == length(v.dom.pos) || error("Expected domain to be a tangent bundle")
  @variables t
  D = Differential(t)
  state_vars = [(@variables $x(t))[1] for x in map(nt -> Symbol(nt[1]), v.dom.pos.ctx)]
  derivatives = interpret(NumR(), v.morphism.update, state_vars)
  eqs = [D(x) ~ dx for (x,dx) in zip(state_vars, derivatives)]
  ODESystem(eqs; name)
end

end
