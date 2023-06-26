module GatlabSciMLExt

using ModelingToolkit
using Gatlab

ModelingToolkit.istree(::Trm) = true
ModelingToolkit.istree(::Type{Trm}) = true

ModelingToolkit.operation(t::Trm) = t.head

ModelingToolkit.arguments(t::Trm) = t.args

ModelingToolkit.similarterm(::Type{Trm}, f::Lvl, args::Vector{Trm}, symtype=Any; metadata=nothing, exprhead=:call) =
  Trm(f, args)

function ModelingToolkit.ODESystem(v::SimpleKleisliLens; name)
  length(v.dom.dir) == length(v.dom.pos) || error("Expected domain to be a tangent bundle")
  @variables t
  D = Differential(t)
  state_vars = [(@variables $x(t))[1] for x in map(nt -> Symbol(nt[1]), v.dom.pos.ctx)]
  param_vars = [(@parameters $p)[1] for p in map(nt -> Symbol(nt[1]), v.codom.dir.ctx)]
  derivatives = interpret.(Ref(NumR()), v.morphism.update, Ref(vcat(state_vars, param_vars)))
  eqs = [D(x) ~ dx for (x,dx) in zip(state_vars, derivatives)]
  ODESystem(eqs, t, state_vars, param_vars; name)
end

function convert_term(t, opmap::AbstractDict, genmap::AbstractDict, into)
  if istree(t)
    op, args = operation(t), arguments(t)
    args′ = convert_term.(args, Ref(opmap), Ref(genmap), Ref(into))
    similarterm(into, opmap[op], args′)
  else
    genmap[t]
  end
end


end
