"""
`sortcheck(ctx::Context, t::AlgTerm)`

Throw an error if a the head of an AlgTerm (which refers to a term constructor)
has arguments of the wrong sort. Returns the sort of the term.
"""
function sortcheck(ctx::Context, t::AlgTerm)::AlgSort
  if isapp(t)
    judgment = ctx[t.body.method] |> getvalue
    if judgment isa AlgTermConstructor
      argsorts = sortcheck.(Ref(ctx), t.body.args)
      argsorts == sortsignature(judgment) || error("Sorts don't match")
      AlgSort(judgment.type)
    end
  elseif isvariable(t)
    type = ctx[t.body] |> getvalue
    AlgSort(type)
  else
    AlgSort(t.body.type)
  end
end

# sortcheck(ctx::Context, t::TermInCtx)::AlgSort =
#   sortcheck(AppendContext(ctx, t.ctx), t.trm)

"""
`sortcheck(ctx::Context, t::AlgType)`

Throw an error if a the head of an AlgType (which refers to a type constructor)
has arguments of the wrong sort.
"""
function sortcheck(ctx::Context, t::AlgType)
  judgment = ctx[t.body.method] |> getvalue
  judgment isa AlgTypeConstructor || error("AlgType method must refer to AlgTypeConstructor: $judgment")
  argsorts = sortcheck.(Ref(ctx), t.body.args)
  expected = AlgSort.(getvalue.(argsof(judgment)))
  argsorts == expected || error("Sorts don't match: $argsorts != $expected")
end

# Equations

""" Implicit equations defined by a context.

This function allows a generalized algebraic theory (GAT) to be expressed as
an essentially algebraic theory, i.e., as partial functions whose domains are
defined by equations.

References:
 - (Cartmell, 1986, Sec 6: "Essentially algebraic theories and categories with
    finite limits")
 - (Freyd, 1972, "Aspects of topoi")

This function gives expressions for computing the elements of `c.context`
  which can be inferred from applying accessor functions to elements of `args`.

Example:
> equations({f::Hom(a,b), g::Hom(b,c)}, {a::Ob, b::Ob, c::Ob}, ThCategory)
ways_of_computing = Dict(a => [dom(f)], b => [codom(f), dom(g)], c => [codom(g)],
                         f => [f], g => [g])
"""
function equations(c::GATContext, args::AbstractVector{Ident}; init=nothing)
  theory = c.theory
  context = c.context
  ways_of_computing = Dict{Ident, Set{AlgTerm}}()
  to_expand = Pair{Ident, AlgTerm}[x => AlgTerm(x) for x in args]

  if !isnothing(init)
    append!(to_expand, pairs(init))
  end

  while !isempty(to_expand)
    x, t = pop!(to_expand)

    if !haskey(ways_of_computing, x)
      ways_of_computing[x] = Set{AlgTerm}()
    end

    push!(ways_of_computing[x], t)

    type = getvalue(context[x])
    typecon = getvalue(theory[type.body.method])

    for (i, arg) in enumerate(type.body.args)
      if isconstant(arg) || isapp(arg)
        continue
      else
        y = arg.body
        @assert y ∈ context
        a = theory.accessors[type.body.method][i]
        acc = getvalue(theory[a])
        expr′ = AlgTerm(getdecl(acc), a, [t])
        push!(to_expand, y => expr′)
      end
    end
  end
  ways_of_computing
end

function equations(theory::GAT, t::TypeInCtx)
  tc = getvalue(theory[headof(t.trm)])
  extended = ScopeList([t.ctx, Scope([Binding{AlgType, Nothing}(nothing, t.trm)])])
  lastx = last(getidents(extended))
  accessor_args = zip(idents(tc.localcontext; lid=tc.args), t.trm.args)
  init = Dict{Ident, AlgTerm}(map(accessor_args) do (accessor, arg)
    hasident(t.ctx, headof(arg)) || error("Case not yet handled")
    headof(arg) => AccessorApplication(accessor, lastx)
  end)
  equations(extended, Ident[], theory; init=init)
end

"""Get equations for a term or type constructor"""
function equations(theory::GAT, x::Ident)
  judgment = getvalue(theory, x)
  equations(GATContext(theory, judgment), idents(judgment.localcontext; lid=judgment.args))
end

function compile(expr_lookup::Dict{Ident}, term::AlgTerm; theorymodule=nothing)
  if isapp(term)
    name = nameof(term.body.head)
    fun = if !isnothing(theorymodule)
      :($theorymodule.$name)
    else
      esc(name)
    end
    Expr(:call, fun, [compile(expr_lookup, arg; theorymodule) for arg in term.body.args]...)
  elseif isvariable(term)
    expr_lookup[term.body]
  elseif isconstant(term)
    term.body.value
  end
end

InCtx(g::GAT, k::Ident) =
  (getvalue(g[k]) isa AlgTermConstructor ? TermInCtx : TypeInCtx)(g, k)

"""
Get the canonical term + ctx associated with a term constructor.
"""
function InCtx{AlgTerm}(g::GAT, k::Ident)
  tcon = getvalue(g[k])
  TermInCtx(tcon.localcontext, AlgTerm(k, AlgTerm.(idents(tcon; lid=tcon.args))))
end

"""
Get the canonical type + ctx associated with a type constructor.
"""
function InCtx{AlgType}(g::GAT, k::Ident)
  tcon = getvalue(g[k])
  TypeInCtx(tcon.localcontext, AlgType(k, AlgTerm.(idents(tcon; lid=tcon.args))))
end

""" Replace idents with AlgTerms. """
function substitute_term(t::T, subst::Dict{Ident,AlgTerm}) where T<:Union{AlgType, AlgTerm}
  if isvar(t)
    dic[t.body]
  elseif isconst(t)
    t
  else
    T(substitute_term(t.body, subst))
  end
end

function substitute_term(ma::MethodApp{AlgTerm}, subst::Dict{Ident, AlgTerm})
  MethodApp(ma.head, ma.method, substitute_term.(ma.args, Ref(subst)))
end
