module GATs
export Constant, AlgTerm, AlgType,
  TypeScope, TypeCtx, AlgSort, AlgSorts,
  AlgTermConstructor, AlgTypeConstructor, AlgAxiom, sortsignature,
  JudgmentBinding, GATSegment, GAT, sortcheck, allnames, sorts, sortname,
  termcons, typecons, accessors, equations, build_infer_expr, compile, 
  InCtx, TermInCtx, TypeInCtx, headof, argsof, argcontext

using ..Scopes
import ..ExprInterop: fromexpr, toexpr

import ..Scopes: retag, rename

using StructEquality
using MLStyle

# TODO: `toexpr` and `fromexpr` from ExprInterop should be defined after each
# term here, and `ExprInterop` should be loaded before this.

# GAT ASTs
##########

"""
We need this to resolve a mutual reference loop; the only subtype is Constant
"""
abstract type AbstractConstant end
abstract type TrmTyp end # AlgTerm or AlgType

"""
`AlgTerm`

One syntax tree to rule all the terms.
Head can be a reference to an AlgTermConstructor, to a Binding{AlgType, Nothing}, or simply an AbstractConstant
"""
@struct_hash_equal struct AlgTerm <: TrmTyp
  head::Union{Ident, AbstractConstant}
  args::Vector{AlgTerm}
  function AlgTerm(head::Union{Ident, AbstractConstant}, args::Vector{AlgTerm}=EMPTY_ARGS)
    new(head, args)
  end
end

const EMPTY_ARGS = AlgTerm[]

fromexpr(c::Context, e, T::Type{<:TrmTyp}; kw...) = 
  fromexpr!(c, e, TypeScope(), T; kw...)


"""
`AlgType`

One syntax tree to rule all the types.
`head` must be reference to a `AlgTypeConstructor`
"""
@struct_hash_equal struct AlgType <: TrmTyp
  head::Ident
  args::Vector{AlgTerm}
  function AlgType(head::Ident, args::Vector{AlgTerm}=EMPTY_ARGS)
    new(head, args)
  end
end

# Common code to Terms and Types
#-------------------------------
headof(t::TrmTyp) = t.head 
argsof(t::TrmTyp) = t.args

rename(tag::ScopeTag, reps::Dict{Symbol,Symbol}, t::T) where T<:TrmTyp =
  T(rename(tag, reps, headof(t)), AlgTerm[rename.(Ref(tag), Ref(reps), argsof(t))...])

function Base.show(io::IO, type::T) where T<:TrmTyp
  print(io, "$(nameof(T))(")
  print(io, toexpr(TypeScope(), type; showing=true))
  print(io, ")")
end

retag(replacements::Dict{ScopeTag,ScopeTag}, t::T) where {T<:TrmTyp} = 
  T(retag(replacements, t.head), AlgTerm[retag.(Ref(replacements), t.args)...])

"""
`Constant`

A Julia value in an algebraic context. Checked elsewhere.
"""
@struct_hash_equal struct Constant <: AbstractConstant
  value::Any
  type::AlgType
end


"""
`AlgSort`

A *sort*, which is essentially a type constructor without arguments
`ref` must be reference to a `AlgTypeConstructor`
"""
@struct_hash_equal struct AlgSort
  ref::Ident
end

AlgSort(t::AlgType) = AlgSort(t.head)

function AlgSort(c::Context, t::AlgTerm)
  if t.head isa AbstractConstant
    AlgSort(t.head.type.head)
  else
    binding = c[t.head]
    value = getvalue(binding)
    if value isa AlgType
      AlgSort(value.head)
    elseif value isa AlgTermConstructor
      AlgSort(value.type.head)
    else
      error("head of AlgTerm $value is not a term constructor or variable")
    end
  end
end

"""
`TypeScope`

A scope where variables are assigned to `AlgType`s, and no overloading is
permitted.
"""
const TypeScope = Scope{AlgType, Nothing}
const TypeCtx = Context{AlgType, Nothing}


# These methods belong above but have `TypeScope` as an argtype
"""
Some expr may have already been bound (e.g. by an explicit context) and thus 
oughtn't be interpreted as `default` type.

In some contexts, we want to interpret ϕ(x::T) as a constant x of type T and 
in others (where constants are not permitted, such as the LHS of a @theorymap 
or in an @theory term constructor) where it can be convenient to annotate 
argument types directly rather than place them in an explicit context.
"""
function fromexpr!(c::Context, e, bound::TypeScope, ::Type{AlgTerm}; constants=true)
  @match e begin
    s::Symbol => begin
      c′ = AppendScope(c, bound)
      scope = getscope(c′, getlevel(c′, s))
      ref = if sigtype(scope) == Union{Nothing, AlgSorts}
        fromexpr(c′, s, Ident; sig=AlgSort[])
      else
        fromexpr(c′, s, Ident)
      end
      AlgTerm(ref)
    end
    Expr(:call, head, argexprs...) => begin
      args = Vector{AlgTerm}(fromexpr!.(Ref(c), argexprs, Ref(bound), Ref(AlgTerm); constants))
      argsorts = AlgSorts(AlgSort.(Ref(AppendScope(c,bound)), args))
      AlgTerm(fromexpr(AppendScope(c,bound), head, Ident; sig=argsorts), args)
    end
    Expr(:(::), val, type) => begin 
      algtype = fromexpr!(c, type, bound, AlgType)
      if constants
        AlgTerm(Constant(val, algtype))
      else 
        Scopes.unsafe_pushbinding!(bound, Binding{AlgType, Nothing}(val, algtype))
        AlgTerm(Ident(gettag(bound), LID(length(bound)), val))
      end
    end
    e::Expr => error("could not parse AlgTerm from $e")
    constant::Constant => AlgTerm(constant)
  end
end

"""
Some expr may have already been bound (e.g. by an explicit context) and thus 
oughtn't be interpreted as `default` type.
"""
function fromexpr!(c::Context, e, bound::TypeScope, ::Type{AlgType}; kw...)::AlgType
  bound = isnothing(bound) ? Dict{Symbol, AlgType}() : bound
  @match e begin
    s::Symbol => AlgType(fromexpr(c, s, Ident))
    Expr(:call, head, args...) =>
      AlgType(fromexpr(c, head, Ident), 
              Vector{AlgTerm}(fromexpr!.(Ref(c), args, Ref(bound), Ref(AlgTerm); kw...)))
    _ => error("could not parse AlgType from $e")
  end
end

"""
`SortScope`

A scope where variables are assigned to `AlgSorts`s, and no overloading is
permitted.
"""
const SortScope = Scope{AlgSort, Nothing}

"""
A type or term with an accompanying type scope, e.g.

 (a,b)::R        (a,b)::Ob
-----------  or  ----------
  a*(a+b)         Hom(a,b)
"""
@struct_hash_equal struct InCtx{T<:TrmTyp}
  ctx::TypeCtx 
  trm::T
end

const TermInCtx = InCtx{AlgTerm}
const TypeInCtx = InCtx{AlgType}

"""
`sortcheck(ctx::Context, t::AlgTerm)`

Throw an error if a the head of an AlgTerm (which refers to a term constructor)
has arguments of the wrong sort. Returns the sort of the term.
"""
function sortcheck(ctx::Context, t::AlgTerm)::AlgSort
  if t.head isa Ident
    judgment = ctx[t.head] |> getvalue
    if judgment isa AlgType
      isempty(t.args) || error("Cannot apply a variable to arguments: $t")
    elseif judgment isa AlgTermConstructor
      argsorts = sortcheck.(Ref(ctx), t.args)
      argsorts == sortsignature(judgment) || error("Sorts don't match")
    else 
      error("Unexpected judgment type $ref for AlgTerm $t")
    end
  end
  return AlgSort(ctx, t)
end


sortcheck(ctx::Context, t::TermInCtx)::AlgSort =
  sortcheck(AppendScope(ctx, t.ctx), t.trm)

"""
`sortcheck(ctx::Context, t::AlgType)`

Throw an error if a the head of an AlgType (which refers to a type constructor)
has arguments of the wrong sort.
"""
function sortcheck(ctx::Context, t::AlgType)
  ref = ctx[t.head] |> getvalue
  ref isa AlgTypeConstructor || error("AlgType head must refer to AlgTypeConstructor: $ref")
  argsorts = sortcheck.(Ref(ctx), t.args)
  expected = AlgSort.([a.head for a in getvalue.(argsof(ref))])
  argsorts == expected || error("Sorts don't match: $argsorts != $expected")
end


abstract type TrmTypConstructor <: HasScope{AlgType, Nothing} end
argsof(t::TrmTypConstructor) = t[t.args]
Scopes.getscope(t::TrmTypConstructor) = t.localcontext

"""
`AlgTypeConstructor`

A declaration of a type constructor
"""
@struct_hash_equal struct AlgTypeConstructor <: TrmTypConstructor
  localcontext::TypeScope
  args::Vector{LID}
end

"""
`AlgTermConstructor`

A declaration of a term constructor
"""
@struct_hash_equal struct AlgTermConstructor <: TrmTypConstructor
  localcontext::TypeScope
  args::Vector{LID}
  type::AlgType
end


sortsignature(tc::Union{AlgTypeConstructor, AlgTermConstructor}) =
  AlgSort.(headof.(getvalue.(argsof(tc))))

"""
`AlgAxiom`

A declaration of an axiom
"""
@struct_hash_equal struct AlgAxiom <: HasScope{AlgType, Nothing}
  localcontext::TypeScope
  type::AlgType
  equands::Vector{AlgTerm}
end
Scopes.getscope(t::AlgAxiom) = t.localcontext

"""
`Judgment`

A judgment is either a type constructor, term constructor, or axiom; a GAT
is composed of a list of judgments.
"""
const Judgment = Union{AlgTypeConstructor, AlgTermConstructor, AlgAxiom}

"""
`AlgSorts`

A description of the argument sorts for a term constructor, used to disambiguate
multiple term constructors of the same name.
"""
const AlgSorts = Vector{AlgSort}

"""
`JudgmentBinding`

A binding of a judgment to a name and possibly a signature.
"""
const JudgmentBinding = Binding{Judgment, Union{AlgSorts, Nothing}}

"""
`GATSegment`

A piece of a GAT, consisting of a scope that binds judgments to names, possibly
disambiguated by argument sorts.
"""
const GATSegment = Scope{Judgment, Union{AlgSorts, Nothing}}

function allnames(seg::GATSegment; aliases=false)
  names = Symbol[]
  for binding in seg
    judgment = getvalue(binding)
    if judgment isa AlgTermConstructor
      push!(names, nameof(binding))
    elseif judgment isa AlgTypeConstructor
      push!(names, nameof(binding))
      for argbinding in argsof(judgment)
        push!(names, nameof(argbinding))
      end
    end
  end
  if aliases
    append!(names, keys(seg.primary))
  end
  names
end

"""
`GAT`

A generalized algebraic theory. Essentially, just consists of a name and a list
of `GATSegment`s, but there is also some caching to make access faster.
Specifically, there is a dictionary to map ScopeTag to position in the list of
segments, and there are lists of all of the identifiers for term constructors,
type constructors, and axioms so that they can be iterated through faster.

GATs allow overloading but not shadowing.
"""
struct GAT <: HasScopeList{Judgment, Union{AlgSorts, Nothing}}
  name::Symbol
  segments::ScopeList{Judgment, Union{AlgSorts, Nothing}}
  termcons::Vector{Ident}
  typecons::Vector{Ident}
  accessors::Dict{Symbol, Set{Ident}}
  axioms::Vector{Ident}
  function GAT(name::Symbol, segments::Vector{GATSegment})
    termcons = Ident[]
    typecons = Ident[]
    axioms = Ident[]
    # Maps a name of an accessor to the type constructors it appears in
    accessors = Dict{Symbol, Set{Ident}}()
    names = Set{Symbol}()
    for segment in segments
      if !isempty(intersect(keys(segment.names), names))
        error("We do not permit shadowing of names between segments of a GAT")
      end
      union!(names, keys(segment.names))
      for (x, judgment) in identvalues(segment)
        if judgment isa AlgTermConstructor
          push!(termcons, x)
        elseif judgment isa AlgTypeConstructor
          push!(typecons, x)
          for arg in argsof(judgment)
            if nameof(arg) ∉ keys(accessors)
              accessors[nameof(arg)] = Set{Ident}()
            end
            push!(accessors[nameof(arg)], x)
          end
        else
          push!(axioms, x)
        end
      end
    end
    if !isempty(intersect(keys(accessors), names))
      error("We do not permit the arguments to type constructors to have the same name as term constructors or type constructors")
    end
    new(name, ScopeList(segments), termcons, typecons, accessors, axioms)
  end

  # This could be faster, but it's not really worth worrying about
  function GAT(name::Symbol, parent::GAT, newsegment::GATSegment)
    GAT(name, [parent.segments.scopes..., newsegment])
  end
end

Base.nameof(theory::GAT) = theory.name
termcons(theory::GAT) = theory.termcons
typecons(theory::GAT) = theory.typecons
accessors(theory::GAT) = theory.accessors
sorts(theory::GAT) = AlgSort.(theory.typecons)

Scopes.getscopelist(c::GAT) = c.segments

function allnames(theory::GAT; aliases=false)
  vcat(allnames.(theory.segments.scopes; aliases)...)
end

function sortname(theory::GAT, type::AlgType)
  canonicalize(theory, type.head)
end

Base.issubset(t1::GAT, t2::GAT) = 
  all(s->hastag(t2, s), gettag.(Scopes.getscopelist(t1).scopes))

## Equations

struct AccessorApplication
  accessor::Ident
  to::Union{Ident, AccessorApplication}
end

const InferExpr = Union{Ident, AccessorApplication}

function build_infer_expr(e::InferExpr; theorymodule=nothing)
  if e isa Ident
    nameof(e)
  else
    name = nameof(e.accessor)
    accessor = if !isnothing(theorymodule)
      :($theorymodule.$name)
    else
      esc(name)
    end
    Expr(:call, accessor, build_infer_expr(e.to; theorymodule))
  end
end

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
  ways_of_computing = Dict{Ident, Set{InferExpr}}()
  to_expand = Pair{Ident, InferExpr}[x => x for x in args]
  if !isnothing(init)
    append!(to_expand, pairs(init))
  end
   
  while !isempty(to_expand)
    x, expr = pop!(to_expand)
    if !haskey(ways_of_computing, x)
      ways_of_computing[x] = Set{InferExpr}()
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
  init = Dict{Ident, InferExpr}(map(accessor_args) do (accessor, arg)
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
  if term.head isa Constant
    term.head.value
  else
    if haskey(expr_lookup, term.head)
      expr_lookup[term.head]
    else
      name = nameof(term.head)
      fun = if !isnothing(theorymodule)
        :($theorymodule.$name)
      else
        esc(name)
      end
      Expr(:call, fun, [compile(expr_lookup, arg; theorymodule) for arg in term.args]...)
    end
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
  head = headof(t)
  tc = getvalue(ctx[head])
  if tc isa AlgType
    tc # base case
  else
    typed_terms = bind_localctx(ctx, t)
    AlgType(headof(tc.type), substitute_term.(argsof(tc.type), Ref(typed_terms)))
  end
end

infer_type(ctx::Context, t::TermInCtx) = infer_type(AppendScope(ctx, t.ctx), t.trm)

"""
Take a term constructor and determine terms of its local context.

This function is mutually recursive with `infer_type`. 
""" 
function bind_localctx(ctx::Context, t::TrmTyp)
  head = headof(t)

  tc = getvalue(ctx[head])
  eqs = equations(ctx, head)

  typed_terms = Dict{Ident, Pair{AlgTerm,AlgType}}()
  for (i,a) in zip(tc.args, t.args)
    tt = (a => infer_type(ctx, a))
    typed_terms[ident(tc, lid=i)] = tt 
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

bind_localctx(ctx::Context, t::InCtx) = bind_localctx(AppendScope(ctx, t.ctx), t.trm)

""" Replace idents with AlgTerms. """
function substitute_term(t::T, dic::Dict{Ident,AlgTerm}) where T<:TrmTyp
  x = headof(t)
  if haskey(dic, x)
    isempty(t.args) || error("Cannot substitute a term with arguments")
    dic[x]
  else 
    T(headof(t), substitute_term.(argsof(t), Ref(dic)))
  end
end

# ExprInterop
#############

function toexpr(c::Context, term::T; kw...) where {T<:TrmTyp}
  if term.head isa Constant
    toexpr(c, term.head; kw...)
  else
    if isempty(term.args)
      toexpr(c, term.head; kw...)
    else
      Expr(:call, toexpr(c, term.head; kw...), toexpr.(Ref(c), term.args; kw...)...)
    end
  end
end

toexpr(c::Context, constant::Constant; kw...) =
  Expr(:(::), constant.value, toexpr(c, constant.type; kw...))


function bindingexprs(c::Context, s::Scope)
  c′ = AppendScope(c, s)
  [Expr(:(::), nameof(b), toexpr(c′, getvalue(b))) for b in s]
end

function toexpr(c::Context, binding::JudgmentBinding)
  judgment = getvalue(binding)
  name = nameof(binding)
  c′ = AppendScope(c, judgment.localcontext)
  head = if judgment isa Union{AlgTypeConstructor, AlgTermConstructor}
    if !isempty(judgment.args)
      Expr(:call, name, nameof.(argsof(judgment))...)
    else
      name
    end
  else
    Expr(:call, :(==), toexpr(c′, judgment.equands[1]), toexpr(c′, judgment.equands[2]))
  end
  headtyped = Expr(:(::), head, judgment isa AlgTypeConstructor ? :TYPE : toexpr(c′, judgment.type))
  if !isempty(judgment.localcontext)
    Expr(:call, :(⊣), headtyped, Expr(:vect, bindingexprs(c, judgment.localcontext)...))
  else
    headtyped
  end
end

"""
Return `nothing` if the binding we parse has already been bound.
"""
function fromexpr(c::Context, e, ::Type{Binding{AlgType, Nothing}})
  @match e begin
    Expr(:(::), name::Symbol, type_expr) => 
        Binding{AlgType, Nothing}(name, fromexpr(c, type_expr, AlgType))
    _ => error("could not parse binding of name to type from $e")
  end
end

"""
Keep track of variables already bound (e.g. in local context) so that they need
not be redefined, e.g. `compose(f,g::Hom(b,c)) ⊣ [(a,b,c)::Ob, f::Hom(a,b)]`
(If `f` were not defined in the local context, it would be parsed as `default`.)
"""
function parsetypescope(c::Context, exprs::AbstractVector)
  scope = TypeScope()
  c′ = AppendScope(c, scope)
  line = nothing
  for expr in exprs
    binding_exprs = @match expr begin
      a::Symbol => [Expr(:(::), a, :default)]
      Expr(:tuple, names...) => [:($name :: default) for name in names]
      Expr(:(::), Expr(:tuple, names...), T) => [:($name :: $T) for name in names]
      :($a :: $T) => [expr]
      l::LineNumberNode => begin
        line = l
        []
      end
      _ => error("invalid binding expression $expr")
    end
    for binding_expr in binding_exprs
      binding = fromexpr(c′, binding_expr, Binding{AlgType, Nothing})
      Scopes.unsafe_pushbinding!(scope, setline(binding, line))
    end
  end
  scope
end

function parseargs!(c::Context, exprs::AbstractVector, scope::TypeScope)
  c′ = AppendScope(c, scope)
  map(exprs) do expr
    binding_expr = @match expr begin
      a::Symbol =>
        if hasident(scope; name=a)
          return getlid(ident(scope; name=a))
        else 
          Expr(:(::), a, :default)
        end
      :($a :: $T) => expr
      _ => error("invalid argument expression $expr")
    end
    binding = fromexpr(c′, binding_expr, Binding{AlgType, Nothing})
    Scopes.unsafe_pushbinding!(scope, binding)
    return LID(length(scope))
  end
end



"""
`axiom=true` adds a `::default` to exprs like `f(a,b) ⊣ [a::A, b::B]`
"""
function normalize_decl(e)
  @match e begin
    :($name := $lhs == $rhs :: $typ ⊣ $ctx) => :((($name := ($lhs == $rhs)) :: $typ) ⊣ $ctx)
    :($lhs == $rhs :: $typ ⊣ $ctx) => :((($lhs == $rhs) :: $typ) ⊣ $ctx)
    :(($lhs == $rhs :: $typ) ⊣ $ctx) => :((($lhs == $rhs) :: $typ) ⊣ $ctx)
    :($trmcon :: $typ ⊣ $ctx) => :(($trmcon :: $typ) ⊣ $ctx)
    :($name := $lhs == $rhs ⊣ $ctx) => :((($name := ($lhs == $rhs))) ⊣ $ctx)
    :($lhs == $rhs ⊣ $ctx) => :(($lhs == $rhs) ⊣ $ctx)
    :($(trmcon::Symbol) ⊣ $ctx) => :(($trmcon :: default) ⊣ $ctx)
    :($f($(args...)) ⊣ $ctx) && if f ∉ [:(==), :(⊣)] end => :(($f($(args...)) :: default) ⊣ $ctx)
    trmcon::Symbol => :($trmcon :: default)
    :($f($(args...))) && if f ∉ [:(==), :(⊣)] end => :($e :: default)
    _ => e
  end
end

function parseaxiom(c::Context, localcontext, type_expr, e; name=nothing)
  @match e begin
    Expr(:call, :(==), lhs_expr, rhs_expr) => begin
      c′ = AppendScope(c, localcontext)
      equands = fromexpr.(Ref(c′), [lhs_expr, rhs_expr], Ref(AlgTerm))
      type = if isnothing(type_expr) 
        infer_type(c′, first(equands))
      else
        fromexpr(c′, type_expr, AlgType)
      end
      axiom = AlgAxiom(localcontext, type, equands)
      JudgmentBinding(name, axiom)
    end
    _ => error("failed to parse equation from $e")
  end
end

"""
parse a term of the following forms:
  compose(f::Hom(a,b), g::Hom(b,c)) ⊣ [(a,b,c)::Ob]
  Hom(dom::Ob, codom::Ob)

Some AlgType information may be in an explicit context, otherwise it comes from
explicitly annotated symbols. For explicit annotations to be registered as such 
rather than parsed as Constants, set kwarg `constants=false`.
"""
function fromexpr(c::Context, e, ::Type{InCtx{T}}; kw...) where T
  (binding, localcontext) = @match e begin
    Expr(:call, :(⊣), binding, Expr(:vect, args...)) => (binding, parsetypescope(c, args))
    e => (e, TypeScope())
  end
  t = fromexpr!(c, binding, localcontext, T; kw...)
  InCtx{T}(localcontext, t)
end

function toexpr(c::Context, tic::InCtx; kw...)  
  c′ = AppendScope(c, tic.ctx)
  etrm = toexpr(c′, tic.trm; kw...)
  flat = Scopes.flatten(tic.ctx)
  ectx = toexpr(AppendScope(c,flat), flat; kw...)
  Expr(:call, :(⊣), etrm, ectx)
end

toexpr(c::Context, ts::TypeScope; kw...) =
  Expr(:vect,[Expr(:(::), nameof(b), toexpr(c, getvalue(b); kw...)) for b in ts]...)

function fromexpr(c::Context, e, ::Type{JudgmentBinding})
  e = normalize_decl(e)

  (binding, localcontext) = @match e begin
    Expr(:call, :(⊣), binding, Expr(:vect, args...)) => (binding, parsetypescope(c, args))
    e => (e, TypeScope())
  end

  c′ = AppendScope(c, localcontext)

  (head, type_expr) = @match binding begin
    Expr(:(::), head, type_expr) => (head, type_expr)
    _ => (binding, nothing)
  end

  @match head begin
    Expr(:(:=), name, equation) => parseaxiom(c, localcontext, type_expr, equation; name)
    Expr(:call, :(==), _, _) => parseaxiom(c, localcontext, type_expr, head)
    _ => begin
      (name, arglist) = @match head begin
        Expr(:call, name, args...) => (name, args)
        name::Symbol => (name, [])
        _ => error("failed to parse head of term constructor $head")
      end
      args = parseargs!(c, arglist, localcontext)
      @match type_expr begin
        :TYPE => begin
          typecon = AlgTypeConstructor(localcontext, args)
          JudgmentBinding(name, typecon)
        end
        _ => begin
          type = fromexpr(c′, type_expr, AlgType)
          termcon = AlgTermConstructor(localcontext, args, type)
          sig = sortsignature(termcon)
          JudgmentBinding(name, termcon, sig)
        end
      end
    end
  end
end

function toexpr(c::Context, seg::GATSegment)
  c′ = AppendScope(c, seg)
  e = Expr(:block)
  for binding in seg
    if !isnothing(getline(binding))
      push!(e.args, getline(binding))
    end
    push!(e.args, toexpr(c′, binding))
  end
  e
end

function fromexpr(c::Context, e, ::Type{GATSegment})
  seg = GATSegment()
  e.head == :block || error("expected a block to pars into a GATSegment, got: $e")
  c′ = AppendScope(c, seg)
  linenumber = nothing
  for line in e.args
    @switch line begin
      @case l::LineNumberNode
        (linenumber = l)
      @case Expr(:macrocall, var"@op", _, aliasexpr)
        lines = @match aliasexpr begin
          Expr(:block, lines...) => lines
          _ => [aliasexpr]
        end
        for line in lines
          @switch line begin
            @case (_::LineNumberNode) 
              nothing
            @case :($alias := $name) 
              Scopes.unsafe_addalias!(seg, name, alias)
            @case _
              error("could not match @op line $line")
          end
        end
      @case Expr(:import, Expr(:(:), Expr(:(.), mod), imports))
        nothing
      @case _ 
        binding = setline(fromexpr(c′, line, JudgmentBinding), linenumber)
        Scopes.unsafe_pushbinding!(seg, binding)
    end
  end
  seg
end

end
