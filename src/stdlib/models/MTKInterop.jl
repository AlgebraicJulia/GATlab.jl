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

function ModelingToolkit.ODESystem(v::SimpleKleisliLens; tspan, name)
  length(v.dom.dir) == length(v.dom.pos) || error("Expected domain to be a tangent bundle")
  @variables t
  D = Differential(t)
  state_vars = [(@variables $x(t))[1] for x in map(nt -> Symbol(nt[1]), v.dom.pos.ctx)]
  param_vars = [(@variables $p)[1] for p in map(nt -> Symbol(nt[1]), v.codom.dir.ctx)]
  derivatives = interpret(NumR(), v.morphism.update, vcat(state_vars, param_vars))
  eqs = [D(x) ~ dx for (x,dx) in zip(state_vars, derivatives)]
  ODESystem(eqs, t, state_vars, param_vars; tspan, name)
end

end
