module GatlabSciMLExt

using ModelingToolkit
using Gatlab

ModelingToolkit.istree(::Trm) = true
ModelingToolkit.istree(::Type{Trm}) = true

ModelingToolkit.operation(t::Trm) = t.head

ModelingToolkit.arguments(t::Trm) = t.args

ModelingToolkit.similarterm(::Type{Trm}, f::Lvl, args::Vector{Trm}, symtype=Any; metadata=nothing, exprhead=:call) =
  Trm(f, args)

ModelingToolkit.istree(::ATrm) = true
ModelingToolkit.istree(::Type{ATrm}) = true

ModelingToolkit.operation(t::ATrm) = t.head

ModelingToolkit.arguments(t::ATrm) = t.args

ModelingToolkit.similarterm(::Type{ATrm}, f::Lvl, args::Vector{ATrm}, symtype=Any; metadata=nothing, exprhead=:call) =
  ATrmCon(f, args)

function ModelingToolkit.ODESystem(v::SimpleKleisliLens; name)
  length(v.dom.dir) == length(v.dom.pos) || error("Expected domain to be a tangent bundle")
  @variables t
  D = Differential(t)
  state_vars = [(@variables $x(t))[1] for x in map(nt -> Symbol(nt[1]), v.dom.pos.ctx)]
  param_vars = [(@parameters $p)[1] for p in map(nt -> Symbol(nt[1]), v.codom.dir.ctx)]
  derivatives = interpret.(Ref(RealModel()), v.morphism.update, Ref(vcat(state_vars, param_vars)))
  eqs = [D(x) ~ dx for (x,dx) in zip(state_vars, derivatives)]
  ODESystem(eqs, t, state_vars, param_vars; name)
end

function convert_term(t, opmap::AbstractDict, genmap::AbstractDict, into; interp_val=(_ -> nothing))
  if istree(t)
    op, args = operation(t), arguments(t)
    args′ = Vector{into}(map(args) do arg
      convert_term(arg, opmap, genmap, into; interp_val)
    end)
    similarterm(into, opmap[op], args′)
  elseif t ∈ keys(genmap)
    genmap[t]
  else
    interp_val(t)
  end
end

const ELEMENTARY_FUNCTION_OPMAP = Dict(
  Base.:(+) => getlevel(ThElementary.:(+)),
  Base.:(*) => getlevel(ThElementary.:(*)),
  Base.:(-) => getlevel(ThElementary.:(-)),
  Base.sin => getlevel(ThElementary.sin),
  Base.cos => getlevel(ThElementary.cos),
  Base.tan => getlevel(ThElementary.tan),
  Base.exp => getlevel(ThElementary.exp),
)


end
