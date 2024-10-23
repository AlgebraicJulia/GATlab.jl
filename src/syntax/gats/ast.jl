# GAT ASTs
##########

export
  ResolvedMethod,
  AlgSort, PrimSort, EqSort, TupleSort,
  TypeApp, TypeEq, NamedTupleType,
  Var, TermApp, Constant, DotAccess, Annot, NamedTupleTerm

struct ResolvedMethod
  head::Ident
  method::Ident
end

Base.nameof(m::ResolvedMethod) = nameof(m.head)

@struct_hash_equal struct AlgNamedTuple{T}
  fields::OrderedDict{Symbol, T}
end

function Base.map(f, t::AlgNamedTuple)
  newfields = OrderedDict((x, f(v)) for (x,v) in t.fields)
  AlgNamedTuple(newfields)
end

"""
`AlgSort`

A *sort*, which is essentially a type constructor without arguments

NOTE: In theory, this could be `Prims.AlgType{Nothing}`... Might be a productive
refactor. However TypeEq references AlgSort, unfortunately, so it's not trivial
to do this.
"""

@sum AlgSort begin
  PrimSort(method::ResolvedMethod)
  EqSort(between::AlgSort)
  TupleSort(tuple::AlgNamedTuple{AlgSort})
end

"""
In order to resolve a mutual-recurrence loop, we make non-recursive
types that are generic over the type of terms.

This has the side-benefit that we can very easily create a data structure
for e-terms by substituting `EId` for `Tm`.
"""
module Prims
using ....Util.SumTypes
import ..GATs: ResolvedMethod, AlgSort, AlgNamedTuple
import ...Scopes: Ident
using MLStyle

@sum AlgType{Tm} begin
  TypeApp(method::ResolvedMethod, args::Vector{Tm})
  TypeEq(sort::AlgSort, equands::Vector{Tm})
  NamedTupleType(tuple::AlgNamedTuple{AlgType{Tm}})
end

"""
The functor instance for AlgType{_}.

Arguments:
- `f::Tm -> Tm′`
- `t::AlgType{Tm}`

The return type Tm′ can either be passed in via into_type or
can be inferred via code_typed.
"""
function Base.map(f, t::AlgType{Tm}; into_type=nothing) where {Tm}
  Tm′ = if isnothing(into_type)
    code_typed(f, Tuple{Tm})[1].second
  else
    into_type
  end
  @match t begin
    TypeApp(method, args) => TypeApp{Tm′}(method, f.(args))
    TypeEq(sort, equands) => TypeEq{Tm′}(sort, f.(equands))
    NamedTupleType(tuple) => NamedTupleType{Tm′}(map(tm -> map(f, tm), tuple))
  end
end

@sum AlgTerm{Tm} begin
  Var(ident::Ident)
  TermApp(method::ResolvedMethod, args::Vector{Tm})
  Constant(value::Any, oftype::AlgType{Tm})
  DotAccess(to::Tm, field::Symbol)
  Annot(on::Tm, type::AlgType{Tm})
  NamedTupleTerm(tuple::AlgNamedTuple{Tm})
end

"""
The functor instance for AlgTerm{_}

Arguments:
- `f::Tm -> Tm′`
- `t::AlgTerm{Tm}`

The return type Tm′ can either be passed in via into_type or
can be inferred via code_typed.
"""
function Base.map(f, t::AlgTerm{Tm}; into_type=nothing) where {Tm}
  Tm′ = if isnothing(into_type)
    code_typed(f, Tuple{Tm})[1].second
  else
    into_type
  end
  @match t begin
    Var(i) => t
    TermApp(method, args) => TermApp{Tm′}(method, f.(args))
    Constant(value, oftype) => Constant{Tm′}(map(f, oftype))
    DotAccess(to, field) => DotAccess{Tm′}(f(to), field)
    Annot(on, type) => Annot{Tm′}(f(on), map(f, type))
    NamedTupleTerm(tuple) => NamedTupleTerm{Tm′}(map(t -> map(f, t), tuple))
  end
end

end

struct AlgTerm
  content::Prims.AlgTerm{AlgTerm}
end

struct AlgType
  content::Prims.AlgType{AlgTerm}
end

_content(t::Union{AlgTerm, AlgType}) = getfield(t, :content)

# Constructors and destructors for AlgTerm/AlgType
##################################################

@active Var(t) begin
  if t isa AlgTerm
    @match _content(t) begin
      Prims.Var(i) => Some(i)
      _ => nothing
    end
  end
end

Var(ident::Ident) =
  AlgTerm(Prims.Var{AlgTerm}(ident))

@active TermApp(t) begin
  if t isa AlgTerm
    @match _content(t) begin
      Prims.TermApp(method, args) => (method, args)
      _ => nothing
    end
  end
end

TermApp(method::ResolvedMethod, args::Vector{AlgTerm}) =
  AlgTerm(Prims.TermApp{AlgTerm}(method, args))

@active Constant(t) begin
  if t isa AlgTerm
    @match _content(t) begin
      Prims.Constant(value, oftype) => (value, AlgType(oftype))
      _ => nothing
    end
  end
end

Constant(value::Any, oftype::AlgType) =
  AlgTerm(Prims.Constant{AlgTerm}(value, oftype.content))

@active DotAccess(t) begin
  if t isa AlgTerm
    @match _content(t) begin
      Prims.DotAccess(to, field) => (to, field)
      _ => nothing
    end
  end
end

DotAccess(to::AlgTerm, field::Symbol) =
  AlgTerm(Prims.DotAccess{AlgTerm}(to, field))

@active Annot(t) begin
  if t isa AlgTerm
    @match _content(t) begin
      Prims.Annot(on, type) => (on, AlgType(type))
      _ => nothing
    end
  end
end

Annot(on::AlgTerm, type::AlgType) =
  AlgTerm(Prims.Annot{AlgTerm}(on, type.content))

@active NamedTupleTerm(t) begin
  if t isa AlgTerm
    @match _content(t) begin
      Prims.NamedTupleTerm(tuple) => Some(tuple)
      _ => nothing
    end
  end
end

NamedTupleTerm(tuple::AlgNamedTuple{AlgTerm}) =
  AlgTerm(Prims.NamedTupleTerm{AlgTerm}(tuple))

@active TypeApp(t) begin
  if t isa AlgType
    @match _content(t) begin
      Prims.TypeApp(method, args) => (method, args)
      _ => nothing
    end
  end
end

TypeApp(method::ResolvedMethod, args::Vector{AlgTerm}) =
  AlgType(Prims.TypeApp{AlgTerm}(method, args))

@active TypeEq(t) begin
  if t isa AlgType
    @match _content(t) begin
      Prims.TypeEq(sort, equands) => (sort, equands)
      _ => nothing
    end
  end
end

TypeEq(sort::AlgSort, equands::Vector{AlgTerm}) =
  AlgType(Prims.TypeEq{AlgTerm}(sort, equands))

@active NamedTupleType(t) begin
  if t isa AlgType
    @match _content(t) begin
      Prims.NamedTupleType(tuple) => Some(map(ty -> AlgType(ty), tuple))
    end
  end
end

NamedTupleType(tuple::AlgNamedTuple{AlgType}) =
  AlgType(Prims.NamedTupleType{AlgTerm}(map(t -> _content(t), tuple)))

# Utility methods for AlgTerm/AlgType
#####################################

function _printvariant(io, v, T, args...)
  show(io, v)
  print(io, "(")
  join(io, args, ", ")
  print(io, ")::")
  show(io, T)
end

function Base.show(io::IO, t::AlgTerm)
  p(v, args...) = _printvariant(io, v, AlgTerm, args...)
  @match t begin
    Var(i) => p(Var, AlgTerm, i)
    TermApp(method, args) => p(TermApp, method, args)
    Constant(value, oftype) => p(Constant, value, oftype)
    DotAccess(to, field) => p(DotAccess, to, field)
    Annot(on, type) => p(Annot, on, type)
    NamedTupleTerm(tuple) => p(NamedTupleTerm, tuple)
  end
end

function Base.show(io::IO, t::AlgType)
  p(v, args...) = _printvariant(io, v, AlgType, args...)
  @match t begin
    TypeApp(method, args) => p(TypeApp, method, args)
    TypeEq(sort, equands) => p(TypeEq, sort, equands)
    NamedTupleType(tuple) => p(NamedTupleType, tuple)
  end
end

"""
Applies `f` to the direct subterms of `t`. See the implementation of `map` for `Prims.AlgTerm`.

Arguments:
- `f::AlgTerm -> AlgTerm`
- `t::AlgTerm`
"""
function Base.map(f, t::AlgTerm)
  AlgTerm(map(f, _content(t); into_type=AlgTerm))
end

"""
Applies `f` to the direct subterms of `t`. See the implementation of `map` for `Prims.AlgType`.

Arguments:
- `f::AlgTerm -> AlgTerm`
- `t::AlgType`
"""
function Base.map(f, t::AlgType)
  AlgTerm(map(f, _content(t); into_type=AlgTerm))
end

# Parsing for AlgTerm/AlgType
#############################


# const EMPTY_ARGS = AlgTerm[]

# rename(tag::ScopeTag, reps::Dict{Symbol,Symbol}, t::AlgTerm) =
#   AlgTerm(rename(tag, reps, t.body))

# retag(reps::Dict{ScopeTag, ScopeTag}, t::AlgTerm) = AlgTerm(retag(reps, t.body))

# reident(reps::Dict{Ident}, t::AlgTerm) = AlgTerm(reident(reps, t.body))

function tcompose(t::AbstractDtry{AlgTerm})
  @match t begin
    Dtrys.Leaf(v) => v
    Dtrys.Node(bs) =>
      NamedTupleTerm(AlgNamedTuple{AlgTerm}(OrderedDict{Symbol, AlgTerm}(
        (n, tcompose(v)) for (n, v) in bs
      )))
    Dtrys.Empty() =>
      NamedTupleTerm(AlgNamedTuple{AlgTerm}(OrderedDict{Symbol, AlgTerm}()))
  end
end

function AlgSort(c::Context, t::AlgTerm)
  t = substitute_funs(c, t)
  @match t begin
    Var(i) => begin
      binding = c[i]
      AlgSort(getvalue(binding))
    end
    Constant(_, oftype) => AlgSort(oftype)
    TermApp(method, args) => begin
      binding = c[method.method]
      value = getvalue(binding)
      if value isa AlgTermConstructor
        AlgSort(value.type)
      elseif value isa AlgFunction
        AlgSort(AppendContext(c, value.localcontext), value.value)
      elseif value isa AlgStruct
        PrimSort(method)
      else
        error("expected a term constructor or a function as the head of a TermApp: got $value")
      end
    end
    DotAccess(to, field) => begin
      parentsort = AlgSort(c, to)
      @match parentsort begin
        PrimSort(method) => begin
          j = getvalue(c[method.method])
          if j isa AlgStruct
            AlgSort(getvalue(j.fields[field]))
          else
            error("tried to access a field of a type which is not a tuple or a struct: $j")
          end
        end
        TupleSort(tuple) => tuple.fields[field]
      end
    end
    Annot(_, type) => AlgSort(type)
    # NamedTupleTerm??
  end
end

function AlgSort(t::AlgType)
  @match t begin
    TypeApp(method, args) => PrimSort(method)
    TypeEq(sort, equands) => EqSort(sort)
    NamedTupleType(tuple) =>
      TupleSort(map(AlgSort, tuple))
  end
end

function tcompose(t::AbstractDtry{AlgType})
  @match t begin
    Dtrys.Node(bs) =>
      NamedTupleType(AlgNamedTuple(OrderedDict(k => tcompose(v) for (k,v) in AbstractTrees.children(t))))
    Dtrys.Leaf(v) => v
    Dtrys.Empty() => NamedTupleType(AlgNamedTuple(OrderedDict{Symbol, AlgType}()))
  end
end

function Prims.getindex(a::AlgTerm, v::DtryVar)
  @match v begin
    Dtrys.Root() => a
    Dtrys.Nested((n, v′)) => getindex(getproperty(a, n), v′)
  end
end

function Base.getproperty(a::AlgTerm, n::Symbol)
  @match a begin
    NamedTupleTerm(tuple) => tuple.fields[n]
    _ => DotAccess(a, n)
  end
end


# Type Contexts
###############

const TypeCtx = Context{AlgType}

"""
A type or term with an accompanying type context, e.g.

 (a,b)::R        (a,b)::Ob
-----------  or  ----------
  a*(a+b)         Hom(a,b)
"""

@struct_hash_equal struct InCtx{T}
  ctx::TypeCtx
  val::T
end

const TermInCtx = InCtx{AlgTerm}
const TypeInCtx = InCtx{AlgType}

Scopes.getvalue(i::InCtx) = i.val
Scopes.getcontext(i::InCtx) = i.ctx
