"""
`sortcheck(ctx::Context, t::AlgTerm)`

Throw an error if a the head of an AlgTerm (which refers to a term constructor)
has arguments of the wrong sort. Returns the sort of the term.
"""
function sortcheck(ctx::Context, t::AlgTerm)
  # The sort, assuming that t is well-formed
  sort_if_correct = AlgSort(ctx, t)
  @match t begin
    TermApp(method, args) => begin
      binding = ctx[method.method]
      value = getvalue(binding)
      arg_sorts = sortcheck.(Ref(ctx), args)
      expected_arg_sorts = if value isa Union{AlgTermConstructor, AlgFunction}
        AlgSort.(getvalue.(value.localcontext[value.args]))
      elseif value isa AlgStruct
        AlgSort.(getvalue.(value.fields))
      else
        error("expected a term constructor or a function as the head of a TermApp: got $value")
      end
      if arg_sorts != expected_arg_sorts
        error("expected argument sorts: $expected_arg_sorts do not match actual argument sorts: $arg_sorts")
      else
        sort_if_correct
      end
    end
    _ => sort_if_correct
  end
end

"""
`sortcheck(ctx::Context, t::AlgType)`

Throw an error if a the head of an AlgType (which refers to a type constructor)
has arguments of the wrong sort.
"""
function sortcheck(ctx::Context, t::AlgType)
  @match t begin
    TypeApp(method, args) => begin
      judgment = ctx[method.method] |> getvalue
      judgment isa AlgTypeConstructor || error("AlgType method must refer to AlgTypeConstructor: $judgment")
      argsorts = sortcheck.(Ref(ctx), args)
      expected = AlgSort.(getvalue.(argsof(judgment)))
      argsorts == expected || error("Sorts don't match: $argsorts != $expected")
    end
  end
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
  # TODO: integrate with namedtupletype
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
  b = bodyof(t.val)
  m = methodof(b)
  newscope = Scope([Binding{AlgType}(nothing, t.val)])
  newterm = AlgTerm(only(getidents(newscope)))
  extended = ScopeList([t.ctx, newscope])
  init = Dict{Ident, AlgTerm}(map(collect(theory.accessors[m])) do (i, acc)
    algacc = getvalue(theory[acc])
    bodyof(b.args[i]) => AlgTerm(algacc.declaration, acc, [newterm])
  end)
  equations(GATContext(theory, extended), Ident[]; init=init)
end

"""Get equations for a term or type constructor"""
function equations(theory::GAT, x::Ident)
  judgment = getvalue(theory, x)
  equations(GATContext(theory, judgment), idents(judgment.localcontext; lid=judgment.args))
end

function compile(expr_lookup::Dict{Ident}, term::AlgTerm;
                 theorymodule=nothing, instance_types=nothing, theory=nothing)
  # TODO: need other cases for AlgTerm
  @match term begin
    Var(i) => begin
      expr_lookup[i]
    end
    TermApp(method, args) => begin
      name = nameof(method.head)
      fun = if !isnothing(theorymodule)
        :($theorymodule.$name)
      else
        esc(name)
      end
      # In the case that we have an old-style instance we need to pass in the
      # return type in order to dispatch a nullary term constructor
      args = if !isnothing(instance_types) && isempty(args)
        termcon = getvalue(theory[method.method])
        [instance_types[AlgSort(termcon.type)]]
      else
        [compile(expr_lookup, arg; theorymodule, instance_types, theory) for arg in args]
      end
      Expr(:call, fun, args...)
    end
    Constant(value, _) => value
  end
end

InCtx(g::GAT, k::Ident) =
  (getvalue(g[k]) isa AlgTermConstructor ? TermInCtx : TypeInCtx)(g, k)

"""
Get the canonical term + ctx associated with a method.
"""
function InCtx{AlgTerm}(g::GAT, k::Ident)
  tcon = getvalue(g[k])
  args = Var.(idents(tcon.localcontext; lid=tcon.args))
  TermInCtx(tcon.localcontext, T(tcon.declaration, k, args))
end

"""
Get the canonical type + ctx associated with a type constructor.
"""
function InCtx{AlgType}(g::GAT, k::Ident)
  tcon = getvalue(g[k])
  args = AlgTerm[Var.(idents(tcon.localcontext; lid=tcon.args))...]
  dec = getvalue(g[k]).declaration
  TypeInCtx(tcon.localcontext, TypApp(ResolvedMethod(dec, k), args))
end

""" Replace idents with AlgTerms. """
function substitute_term(t::T, subst::Dict{Ident,AlgTerm}) where T
  @match t begin
    Var(i) => get(subst, i, Var(i))
    TermApp(method, args) => TermApp(method, substitute_term.(args, Ref(subst)))
    DotAccess(t, field) => DotAccess(substitute_term(t, subst), field)
    NamedTupleTerm(tuple) => NamedTupleTerm(map(t -> substitute_term(t, subst), tuple))
    # TODO: also substitute in type
    Annot(t, type) => Annot(substitute_term(t, subst), type)
    # TODO: Constant
  end
end

"""Replace all functions with their desugared expressions"""
function substitute_funs(ctx::Context, t::AlgTerm)
  @match t begin
    TermApp(method, args) => begin
      m = getvalue(ctx[method.method])
      if m isa AlgTermConstructor || m isa AlgStruct
        args = substitute_funs.(Ref(ctx), argsof(b))
        AlgTerm(MethodApp{AlgTerm}(headof(b), methodof(b), args))
      elseif m isa AlgFunction
        subst = Dict(zip(idents(m.localcontext; lid=m.args), argsof(b)))
        substitute_term(m.value, subst)
      end
    end
    Var(_) => t
    Constant(_, _) => t
    DotAccess(t, field) => DotAccess(substitute_funs(ctx, t), field)
    # TODO: also substitute in type
    Annot(t, type) => Annot(substitute_funs(ctx, t), type)
    # TODO: namedtuple
  end
end

# What does this even mean?? What is the type of f supposed to be??

# Base.map(f, t::AlgTerm) = AlgTerm(map(f, bodyof(t)))

# Base.map(f, b::MethodApp{AlgTerm}) = MethodApp{AlgTerm}(headof(b), methodof(b), map(f, argsof(b)))

# Base.map(f, b::AlgDot) = AlgDot(b.head, f(b.body))

# Base.map(f, b::AlgAnnot) = AlgAnnot(f(b.term), b.type)

# Base.map(f, b::AlgNamedTuple{AlgTerm}) =
#   AlgNamedTuple{AlgTerm}(OrderedDict{Symbol, AlgTerm}(n => f(v) for (n, v) in b.fields))

# Base.map(f, b::Ident) = b

# Base.map(f, b::Constant) = b
