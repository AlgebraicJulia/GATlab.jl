module GATs
export Constant, AlgTerm, AlgType,
  TypeScope, AlgSort, AlgSorts,
  AlgTermConstructor, AlgTypeConstructor, AlgAxiom, sortsignature,
  JudgmentBinding, GATSegment, GAT, sortcheck, allnames, sorts, sortname,
  termcons, typecons, accessors, equations, build_infer_expr, compile, 
  TermInCtx, headof, argsof, argcontext

using ..Scopes
using ..ExprInterop

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
  head::Union{Reference, AbstractConstant}
  args::Vector{AlgTerm}
  function AlgTerm(head::Union{Reference, AbstractConstant}, args::Vector{AlgTerm}=EMPTY_ARGS)
    new(head, args)
  end
end

const EMPTY_ARGS = AlgTerm[]

AlgTerm(head::Ident, args::Vector{AlgTerm}=EMPTY_ARGS) = AlgTerm(Reference(head), args)

"""
Some expr may have already been bound (e.g. by an explicit context) and thus 
oughtn't be interpreted as `default` type.
"""
function ExprInterop.fromexpr(c::Context, e, ::Type{AlgTerm}; bound=nothing)
  bound = isnothing(bound) ? Dict{Symbol,AlgType}() : bound
  @match e begin
    s::Symbol => begin
      scope = getscope(c, getlevel(c, s))
      ref = if sigtype(scope) == Union{Nothing, AlgSorts}
        fromexpr(c, s, Reference; sig=AlgSort[])
      else
        fromexpr(c, s, Reference)
      end
      AlgTerm(ref)
    end
    Expr(:call, head, argexprs...) => begin
      args = Vector{AlgTerm}(fromexpr.(Ref(c), argexprs, Ref(AlgTerm)))
      argsorts = AlgSorts(AlgSort.(Ref(c), args))
      AlgTerm(fromexpr(c, head, Reference; sig=argsorts), args)
    end
    Expr(:(::), val, type) => 
      AlgTerm(Constant(val, get(bound, val, fromexpr(c, type, AlgType; bound=bound))))
    e::Expr => error("could not parse AlgTerm from $e")
    constant::Constant => AlgTerm(constant)
    i::Ident => AlgTerm(Reference(i))
  end
end


"""
`AlgType`

One syntax tree to rule all the types.
`head` must be reference to a `AlgTypeConstructor`
"""
@struct_hash_equal struct AlgType <: TrmTyp
  head::Reference
  args::Vector{AlgTerm}
  function AlgType(head::Reference, args::Vector{AlgTerm}=EMPTY_ARGS)
    new(head, args)
  end
end

AlgType(head::Ident, args::Vector{AlgTerm}=EMPTY_ARGS) = AlgType(Reference(head), args)

"""
Some expr may have already been bound (e.g. by an explicit context) and thus 
oughtn't be interpreted as `default` type.
"""
function ExprInterop.fromexpr(c::Context, e, ::Type{AlgType}; bound=nothing)::AlgType
  bound = isnothing(bound) ? Dict{Symbol, AlgType}() : bound
  @match e begin
    s::Symbol => AlgType(fromexpr(c, s, Reference))
    Expr(:call, head, args...) =>
      AlgType(fromexpr(c, head, Reference), fromexpr.(Ref(c), args, Ref(AlgTerm); bound=bound))
    _ => error("could not parse AlgType from $e")
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
  print(io, toexpr(EmptyContext(), type; showing=true))
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
  ref::Reference
end

AlgSort(i::Ident) = AlgSort(Reference(i))
AlgSort(t::AlgType) = AlgSort(t.head)

function AlgSort(c::Context, t::AlgTerm)
  if t.head isa AbstractConstant
    AlgSort(t.head.type.head)
  else
    binding = c[only(t.head)]
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

"""
`SortScope`

A scope where variables are assigned to `AlgSorts`s, and no overloading is
permitted.
"""
const SortScope = Scope{AlgSort, Nothing}

"""
A term with an accompanying type scope, e.g.

 (a,b)::R
-----------
  a*(a+b)
"""
@struct_hash_equal struct TermInCtx
  ctx::TypeScope 
  trm::AlgTerm
end


"""
`sortcheck(ctx::Context, t::AlgTerm)`

Throw an error if a the head of an AlgTerm (which refers to a term constructor)
has arguments of the wrong sort. Returns the sort of the term.
"""
function sortcheck(ctx::Context, t::AlgTerm)::AlgSort
  if t.head isa Reference
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
  expected = AlgSort.([a.head for a in getvalue.(ref.args)])
  argsorts == expected || error("Sorts don't match: $argsorts != $expected")
end

"""
`AlgTypeConstructor`

A declaration of a type constructor
"""
@struct_hash_equal struct AlgTypeConstructor
  localcontext::TypeScope
  args::TypeScope
end

"""
`AlgTermConstructor`

A declaration of a term constructor
"""
@struct_hash_equal struct AlgTermConstructor
  localcontext::TypeScope
  args::TypeScope
  type::AlgType
end

sortsignature(tc::Union{AlgTypeConstructor, AlgTermConstructor}) =
  AlgSort.([a.head for a in getvalue.(tc.args)])

"""Local context of an AlgTermConstructor, including the arguments themselves"""
argcontext(t::Union{AlgTypeConstructor,AlgTermConstructor}) = 
  t.localcontext + t.args

"""
`AlgAxiom`

A declaration of an axiom
"""
@struct_hash_equal struct AlgAxiom
  localcontext::TypeScope
  type::AlgType
  equands::Vector{AlgTerm}
end

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
      if aliases
        append!(names, getaliases(binding))
      else
        push!(names, nameof(binding))
      end
    elseif judgment isa AlgTypeConstructor
      if aliases
        append!(names, getaliases(binding))
      else
        push!(names, nameof(binding))
      end
      for argbinding in judgment.args
        push!(names, nameof(argbinding))
      end
    end
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
          for arg in judgment.args
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
  canonicalize(theory, only(type.head))
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
function equations(args::TypeScope, localcontext::TypeScope, theory::GAT)
  ways_of_computing = Dict{Ident, Set{InferExpr}}()
  to_expand = Pair{Ident, InferExpr}[x => x for x in idents(args)]

  context = ScopeList([args, localcontext])
   
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
      elseif first(arg.head) ∈ theory
        continue
      else
        @assert first(arg.head) ∈ context
        a = ident(xtypecon.args; lid=LID(i))
        y = first(arg.head)
        expr′ = AccessorApplication(a, expr)
        push!(to_expand, y => expr′)
      end
    end
  end
  ways_of_computing
end

"""Get equations for a term or type constructor"""
equations(theory::GAT, x::Ident) = let x = getvalue(theory[x]);
  equations(x.args, x.localcontext, theory) 
end

function compile(expr_lookup::Dict{Reference}, term::AlgTerm; theorymodule=nothing)
  if term.head isa Constant
    term.head.value
  else
    if haskey(expr_lookup, term.head)
      expr_lookup[term.head]
    else
      name = nameof(only(term.head))
      fun = if !isnothing(theorymodule)
        :($theorymodule.$name)
      else
        esc(name)
      end
      Expr(:call, fun, [compile(expr_lookup, arg; theorymodule) for arg in term.args]...)
    end
  end
end

"""Get the canonical term associated with a term constructor"""
function TermInCtx(g::GAT, k::Ident)
  tcon = getvalue(g[k])
  lc = argcontext(tcon)
  ids = reverse(reverse(idents(lc))[1:(length(tcon.args))])
  TermInCtx(lc, AlgTerm(Reference(k), AlgTerm.(ids)))
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
function infer_type(theory::GAT, t::TermInCtx)
  head = only(headof(t.trm))
  if hasident(t.ctx, head) 
    getvalue(t.ctx[head]) # base case
  else
    tc = getvalue(theory[head])
    eqs = equations(theory, head)
    typed_terms = Dict{Ident, Pair{AlgTerm,AlgType}}()
    for (i,a) in zip(tc.args, t.trm.args)
      tt = (a => infer_type(theory, TermInCtx(t.ctx, a)))
      typed_terms[ident(tc.args, name=nameof(i))] = tt 
    end
    for lc_arg in reverse(idents(tc.localcontext))
      # one way of determining lc_arg's value
      filt(e) = e isa AccessorApplication && e.to isa Ident
      app = first(filter(filt, eqs[lc_arg])) 

      inferred_term = typed_terms[app.to][2].args[app.accessor.lid.val]
      inferred_type = infer_type(theory, TermInCtx(t.ctx,inferred_term))
      typed_terms[lc_arg] = inferred_term => inferred_type
    end
    AlgType(headof(tc.type), map(argsof(tc.type)) do arg
      substitute_term(arg, Dict([k=>v[1] for (k,v) in pairs(typed_terms)]))
    end)
  end
end

"""
Take a term constructor and determine terms of its local context.

This function is mutually recursive with `infer_type`. 
""" 
function bind_localctx(theory::GAT, t::TermInCtx)
  head = only(headof(t.trm))

  tc = getvalue(theory[head])
  eqs = equations(theory, head)

  typed_terms = Dict{Ident, Pair{AlgTerm,AlgType}}()
  for (i,a) in zip(tc.args, t.trm.args)
    tt = (a => infer_type(theory, TermInCtx(t.ctx, a)))
    typed_terms[ident(tc.args, name=nameof(i))] = tt 
  end

  for lc_arg in reverse(idents(tc.localcontext))
    # one way of determining lc_arg's value
    filt(e) = e isa AccessorApplication && e.to isa Ident
    app = first(filter(filt, eqs[lc_arg])) 
    inferred_term = typed_terms[app.to][2].args[app.accessor.lid.val]
    inferred_type = infer_type(theory, TermInCtx(t.ctx,inferred_term))
    typed_terms[lc_arg] = inferred_term => inferred_type
  end

  Dict([k=>v[1] for (k,v) in pairs(typed_terms)])
end

""" Replace idents with AlgTerms. """
function substitute_term(t::TrmTyp, dic::Dict{Ident,AlgTerm})
  iden = only(headof(t))
  if haskey(dic, iden)
    isempty(t.args) || error("Cannot substitute a term with arguments")
    dic[iden]
  else 
    AlgTerm(headof(t), substitute_term.(argsof(t), Ref(dic)))
  end
end

# ExprInterop
#############

function ExprInterop.toexpr(c::Context, term::T; kw...) where {T<:TrmTyp}
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

ExprInterop.toexpr(c::Context, constant::Constant; kw...) =
  Expr(:(::), constant.value, toexpr(c, constant.type; kw...))


ExprInterop.toexpr(c::Context, term::AlgSort; kw...) = 
  ExprInterop.toexpr(c, term.ref; kw...)

ExprInterop.fromexpr(c::Context, e, ::Type{AlgSort}) = 
  AlgSort(ExprInterop.fromexpr(c, e, Reference))


function bindingexprs(c::Context, s::Scope)
  c′ = AppendScope(c, s)
  [Expr(:(::), nameof(b), toexpr(c′, getvalue(b))) for b in s]
end

function ExprInterop.toexpr(c::Context, binding::JudgmentBinding)
  judgment = getvalue(binding)
  name = nameof(binding)
  c′ = AppendScope(c, judgment.localcontext)
  head = if judgment isa Union{AlgTypeConstructor, AlgTermConstructor}
    if !isempty(judgment.args)
      Expr(:call, name, bindingexprs(c′, judgment.args)...)
    else
      name
    end
  else
    Expr(:call, :(==), toexpr(c′, judgment.equands[1]), toexpr(c′, judgment.equands[2]))
  end
  c″ = judgment isa AlgTermConstructor ? AppendScope(c′, judgment.args) : c′
  headtyped = Expr(:(::), head, judgment isa AlgTypeConstructor ? :TYPE : toexpr(c″, judgment.type))
  if !isempty(judgment.localcontext)
    Expr(:call, :(⊣), headtyped, Expr(:vect, bindingexprs(c, judgment.localcontext)...))
  else
    headtyped
  end
end

"""
Return `nothing` if the binding we parse has already been bound.
"""
function ExprInterop.fromexpr(c::Context, e, ::Type{Binding{AlgType, Nothing}})
  @match e begin
    Expr(:(::), name::Symbol, type_expr) => 
        Binding{AlgType, Nothing}(name, Set([name]), fromexpr(c, type_expr, AlgType))
    _ => error("could not parse binding of name to type from $e")
  end
end

"""
Keep track of variables already bound (e.g. in local context) so that they need
not be redefined, e.g. `compose(f,g::Hom(b,c)) ⊣ [(a,b,c)::Ob, f::Hom(a,b)]`
(If `f` were not defined in the local context, it would be parsed as `default`.)
"""
function parsetypescope(c::Context, exprs::AbstractVector; bound=nothing)
  bound = isnothing(bound) ? Set{Symbol}() : bound
  scope = TypeScope()
  c′ = AppendScope(c, scope)
  line = nothing
  for expr in exprs
    binding_exprs = @match expr begin
      a::Symbol => a ∈ bound ? [] : [:($a :: default)]
      Expr(:tuple, names...) => [:($name :: default) for name in names if name ∉ bound]
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

"""
`axiom=true` adds a `::default` to exprs like `f(a,b) ⊣ [a::A, b::B]`
"""
function normalize_decl(e; axiom=false)
  @match e begin
    :($name := $lhs == $rhs :: $typ ⊣ $ctx) => :((($name := ($lhs == $rhs)) :: $typ) ⊣ $ctx)
    :($lhs == $rhs :: $typ ⊣ $ctx) => :((($lhs == $rhs) :: $typ) ⊣ $ctx)
    :(($lhs == $rhs :: $typ) ⊣ $ctx) => :((($lhs == $rhs) :: $typ) ⊣ $ctx)
    :($lhs == $rhs ⊣ $ctx) => :((($lhs == $rhs) :: default) ⊣ $ctx)
    :($trmcon :: $typ ⊣ $ctx) => :(($trmcon :: $typ) ⊣ $ctx)
    :($trmcon ⊣ $ctx) => axiom ? :(($trmcon :: default) ⊣ $ctx) : e
    e => e
  end
end

function parseaxiom(c::Context, localcontext, type_expr, e; name=nothing)
  @match e begin
    Expr(:call, :(==), lhs_expr, rhs_expr) => begin
      equands = fromexpr.(Ref(c), [lhs_expr, rhs_expr], Ref(AlgTerm))
      type = fromexpr(c, type_expr, AlgType)
      axiom = AlgAxiom(localcontext, type, equands)
      JudgmentBinding(name, isnothing(name) ? Set{Symbol}() : Set([name]), axiom)
    end
    _ => error("failed to parse equation from $e")
  end
end

function ExprInterop.fromexpr(c::Context, e, ::Type{TermInCtx})
  (binding, localcontext) = @match normalize_decl(e) begin
    Expr(:call, :(⊣), binding, Expr(:vect, args...)) => (binding, parsetypescope(c, args))
    e => (e, TypeScope())
  end
  c′ = AppendScope(c, localcontext)
  bound = Dict([nameof(b) => getvalue(b) for b in getbindings(localcontext)])
  t = ExprInterop.fromexpr(c′, binding, AlgTerm; bound=bound)
  TermInCtx(localcontext, t)
end

ExprInterop.toexpr(c::Context, tic::TermInCtx) = let c′=AppendScope(c,tic.ctx);
  Expr(:call, :(⊣), ExprInterop.toexpr(c′, tic.trm), ExprInterop.toexpr(c′, tic.ctx))
end

ExprInterop.toexpr(c::Context, ts::TypeScope) =
  Expr(:vect,[Expr(:(::), nameof(b), toexpr(c, getvalue(b))) for b in ts]...)

ExprInterop.toexpr(c::Context, at::Binding{AlgType, Nothing}) =
  Expr(:(::), nameof(at), ExprInterop.toexpr(c, getvalue(at)))

function ExprInterop.fromexpr(c::Context, e, ::Type{JudgmentBinding})
  (binding, localcontext) = @match normalize_decl(e; axiom=true) begin
    Expr(:call, :(⊣), binding, Expr(:vect, args...)) => (binding, parsetypescope(c, args))
    e => (e, TypeScope())
  end

  c′ = AppendScope(c, localcontext)

  (head, type_expr) = @match binding begin
    Expr(:(::), head, type_expr) => (head, type_expr)
    _ => (binding, :default)
  end

  @match head begin
    Expr(:(:=), name, equation) => parseaxiom(c′, localcontext, type_expr, equation; name)
    Expr(:call, :(==), _, _) => parseaxiom(c′, localcontext, type_expr, head)
    _ => begin
      (name, arglist) = @match head begin
        Expr(:call, name, args...) => (name, args)
        name::Symbol => (name, [])
        _ => error("failed to parse head of term constructor $call")
      end
      args = parsetypescope(c′, arglist; bound=Set(nameof.(localcontext)))
      @match type_expr begin
        :TYPE => begin
          typecon = AlgTypeConstructor(localcontext, args)
          JudgmentBinding(name, Set([name]), typecon)
        end
        _ => begin
          c″ = AppendScope(c′, args)
          type = fromexpr(c″, type_expr, AlgType)
          termcon = AlgTermConstructor(localcontext, args, type)
          argsorts = AlgSort.(getvalue.(args))
          JudgmentBinding(name, Set([name]), termcon, argsorts)
        end
      end
    end
  end
end

function ExprInterop.toexpr(c::Context, seg::GATSegment)
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

function ExprInterop.fromexpr(c::Context, e, ::Type{GATSegment})
  seg = GATSegment()
  e.head == :block || error("expected a block to pars into a GATSegment, got: $e")
  c′ = AppendScope(c, seg)
  linenumber = nothing
  for line in e.args
    @match line begin
      l::LineNumberNode => (linenumber = l)
      Expr(:macrocall, var"@op", _, aliasexpr) => begin
        lines = @match aliasexpr begin
          Expr(:block, lines...) => lines
          _ => [aliasexpr]
        end
        for line in lines
          @match line begin
            _::LineNumberNode => nothing
            :($alias := $name) => Scopes.unsafe_addalias!(seg, name, alias)
            _ => error("could not match @op line $line")
          end
        end
      end
      _ => begin
        binding = setline(fromexpr(c′, line, JudgmentBinding), linenumber)
        Scopes.unsafe_pushbinding!(seg, binding)
      end
    end
  end
  seg
end

end
