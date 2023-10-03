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
#   sortcheck(AppendScope(ctx, t.ctx), t.trm)

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

This function gives expressions for computing each of the elements of `context`
  from the `args`, as well as checking that the args are well-typed.

Example:
> equations({f::Hom(a,b), g::Hom(b,c)}, {a::Ob, b::Ob, c::Ob}, ThCategory)
ways_of_computing = Dict(a => [dom(f)], b => [codom(f), dom(g)], c => [codom(g)],
                         f => [f], g => [g])

Algorithm:

Start from the arguments. We know how to compute each of the arguments; they are
given. Each argument tells us how to compute other arguments, and also elements
of the context
"""
function equations(context::TypeCtx, args::AbstractVector{Ident}, theory::Context; init=nothing)
  ways_of_computing = Dict{Ident, Set{AlgTerm}}()
  to_expand = Pair{Ident, AlgTerm}[x => x for x in args]
  if !isnothing(init)
    append!(to_expand, pairs(init))
  end

  while !isempty(to_expand)
    x, expr = pop!(to_expand)
    if !haskey(ways_of_computing, x)
      ways_of_computing[x] = Set{AlgTerm}()
    end
    push!(ways_of_computing[x], expr)

    xtype = getvalue(context[x])
    xtypecon = getvalue(theory[xtype.head])

    for (i, arg) in enumerate(xtype.args)
      if arg.head isa Constant
        continue
      elseif arg.head ∈ theory
        continue
      else
        @assert arg.head ∈ context
        a = ident(xtypecon; lid=LID(i))
        y = arg.head
        expr′ = AccessorApplication(a, expr)
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
equations(theory::Context, x::Ident) = let x = getvalue(theory[x]);
  equations(x, idents(x; lid=x.args),theory)
end

function compile(expr_lookup::Dict{Ident}, term::AlgTerm; theorymodule=nothing)
  if isapp(term)
    name = nameof(term.body.head)
    fun = if !isnothing(theorymodule)
      :($theorymodule.$name)
    else
      esc(name)
    end
    Expr(:call, fun, [compile(expr_lookup, arg; theorymodule) for arg in term.args]...)
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


"""
Infer the type of the term of a term. If it is not in context, recurse on its
arguments. The term constructor's output type yields the resulting type once
its localcontext variables are substituted with the relevant AlgTerms.

              (x,y,z)::Ob, p::Hom(x,y), q::Hom(y,z)
E.g. given    --------------------------------------
                           id(x)⋅(p⋅q)

                 (a,b,c)::Ob, f::Hom(a,b), g::Hom(b,c)
and output type:  ------------------------------------
                              Hom(a,c)

We first recursively find `{id(x) => Hom(x,x), p⋅q => Hom(x,z)}`. We ultimately
want an AlgTerm for everything in the output type's context such that we can
substitute into `Hom(a,c)` to get the final answer. It will help to also compute
the AlgType for everything in the context. We work backwards, since we start by
knowing `{f => id(x)::Hom(x,x), g=> p⋅q :: Hom(x,z)}`. For `a` `b` and `c`,
we use `equations` which tell us, e.g., that `a = dom(f)`. So we can grab the
first argument of the *type* of `f` (i.e. grab `x` from `Hom(x,x)`).
"""
function infer_type(ctx::Context, t::AlgTerm)
  if isvariable(t)
    getvalue(ctx[head])
  elseif isconstant(t)
    t.body.type
  else
    typed_terms = bind_localctx(ctx, t.body)
    tc = ctx[t.body.method]
    substitute_type(tc.type, typed_terms)
  end
end

infer_type(ctx::Context, t::TermInCtx) = infer_type(AppendContext(ctx, t.ctx), t.trm)

"""
Take a term constructor and determine terms of its local context.

This function is mutually recursive with `infer_type`.
"""
function bind_localctx(ctx::Context, t::MethodApp{AlgTerm})
  tc = getvalue(ctx[t.method])

  eqs = equations(ctx, head)

  typed_terms = Dict{Ident, Pair{AlgTerm,AlgType}}()
  for (i,a) in zip(tc.args, t.args)
    tt = (a => infer_type(ctx, a))
    typed_terms[ident(tc; lid=i)] = tt
  end

  for lc_arg in reverse(getidents(tc))
    if getlid(lc_arg) ∈ tc.args
      continue
    end
    # one way of determining lc_arg's value
    filt(e) = e isa AccessorApplication && e.to isa Ident
    app = first(filter(filt, eqs[lc_arg]))
    inferred_term = typed_terms[app.to][2].args[app.accessor.lid.val]
    inferred_type = infer_type(ctx, inferred_term)
    typed_terms[lc_arg] = inferred_term => inferred_type
  end

  Dict([k=>v[1] for (k,v) in pairs(typed_terms)])
end

bind_localctx(ctx::Context, t::InCtx) = bind_localctx(AppendContext(ctx, t.ctx), t.trm)

""" Replace idents with AlgTerms. """
function substitute_term(t::T, dic::Dict{Ident,AlgTerm}) where T<:Union{AlgType, AlgTerm}
  if isvar(t)
    dic[t.body]
  elseif isconst(t)
    t
  else
    T(substitute_term(t.body, dic))
  end
end

function substitute_term(ma::MethodApp{AlgTerm}, dic::Dict{Ident, AlgTerm})
  MethodApp(ma.head, ma.method, substitute_term.(ma.args, Ref(dic)))
end
