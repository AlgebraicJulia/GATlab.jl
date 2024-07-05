# GAT ASTs
##########

export
  AlgSort, PrimSort, TupleSort,
  TypeApp, TypeEq, NamedTupleType,
  Var, TermApp, Constant, DotAccess, Annot, NamedTupleTerm

struct ResolvedMethod
  head::Ident
  method::Ident
end

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
"""

@sum AlgSort begin
  PrimSort(method::ResolvedMethod)
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

@sum AlgType{Tm} begin
  TypeApp(method::ResolvedMethod, args::Vector{Tm})
  TypeEq(sort::AlgSort, equands::Vector{Tm})
  NamedTupleType(tuple::AlgNamedTuple{AlgType{Tm}})
end

@sum AlgTerm{Tm} begin
  Var(ident::Ident)
  TermApp(method::ResolvedMethod, args::Vector{Tm})
  Constant(value::Any, oftype::AlgType{Tm})
  DotAccess(to::Tm, field::Symbol)
  Annot(on::Tm, type::AlgType{Tm})
  NamedTupleTerm(tuple::AlgNamedTuple{Tm})
end
end

struct AlgTerm
  content::Prims.AlgTerm{AlgTerm}
end

struct AlgType
  content::Prims.AlgType{AlgTerm}
end

# Constructors and destructors for AlgTerm/AlgType
##################################################

@active Var(t) begin
  if t isa AlgTerm
    @match t.content begin
      Prims.Var(i) => Some(i)
      _ => nothing
    end
  end
end

Var(ident::Ident) =
  AlgTerm(Prims.Var{AlgTerm}(ident))

@active TermApp(t) begin
  if t isa AlgTerm
    @match t.content begin
      Prims.TermApp(method, args) => (method, args)
      _ => nothing
    end
  end
end

TermApp(method::ResolvedMethod, args::Vector{AlgTerm}) =
  AlgTerm(Prims.TermApp{AlgTerm}(method, args))

@active Constant(t) begin
  if t isa AlgTerm
    @match t.content begin
      Prims.Constant(value, oftype) => (value, AlgType(oftype))
      _ => nothing
    end
  end
end

Constant(value::Any, oftype::AlgType) =
  AlgTerm(Prims.Constant{AlgTerm}(value, oftype.content))

@active DotAccess(t) begin
  if t isa AlgTerm
    @match t.content begin
      Prims.DotAccess(to, field) => (to, field)
      _ => nothing
    end
  end
end

DotAccess(to::AlgTerm, field::Symbol) =
  AlgTerm(Prims.DotAccess{AlgTerm}(to, field))

@active Annot(t) begin
  if t isa AlgTerm
    @match t.content begin
      Prims.Annot(on, type) => (on, type)
      _ => nothing
    end
  end
end

Annot(on::AlgTerm, type::AlgType) =
  AlgTerm(Prims.Annot{AlgTerm}(on, type.content))

@active NamedTupleTerm(t) begin
  if t isa AlgTerm
    @match t.content begin
      Prims.NamedTupleTerm(tuple) => Some(tuple)
      _ => nothing
    end
  end
end

NamedTupleTerm(tuple::AlgNamedTuple{AlgTerm}) =
  AlgTerm(Prims.NamedTupleTerm{AlgTerm}(tuple))

@active TypeApp(t) begin
  if t isa AlgType
    @match t.content begin
      Prims.TypeApp(method, args) => (method, args)
      _ => nothing
    end
  end
end

TypeApp(method::ResolvedMethod, args::Vector{AlgTerm}) =
  AlgType(Prims.TypeApp{AlgTerm}(method, args))

@active TypeEq(t) begin
  if t isa AlgType
    @match t.content begin
      Prims.TypeEq(sort, equands) => (sort, equands)
      _ => nothing
    end
  end
end

TypeEq(sort::AlgSort, equands::Vector{AlgTerm}) =
  AlgType(Prims.TypeEq{AlgTerm}(sort, equands))

@active NamedTupleType(t) begin
  if t isa AlgType
    @match t.content begin
      Prims.NamedTupleType(tuple) => map(ty -> AlgType(ty), tuple)
    end
  end
end

NamedTupleType(tuple::AlgNamedTuple{AlgType}) =
  AlgType(Prims.NamedTupleType{AlgTerm}(map(t -> t.content, tuple)))

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

# Parsing for AlgTerm/AlgType
#############################


# const EMPTY_ARGS = AlgTerm[]

# rename(tag::ScopeTag, reps::Dict{Symbol,Symbol}, t::AlgTerm) =
#   AlgTerm(rename(tag, reps, t.body))

# retag(reps::Dict{ScopeTag, ScopeTag}, t::AlgTerm) = AlgTerm(retag(reps, t.body))

# reident(reps::Dict{Ident}, t::AlgTerm) = AlgTerm(reident(reps, t.body))

# function tcompose(t::AbstractDtry{AlgTerm})
#   @match t begin
#     Dtrys.Leaf(v) => v
#     Dtrys.Node(bs) =>
#       AlgTerm(AlgNamedTuple{AlgTerm}(OrderedDict{Symbol, AlgTerm}(
#         (n, tcompose(v)) for (n, v) in bs
#       )))
#     Dtrys.Empty() =>
#       AlgTerm(AlgNamedTuple{AlgTerm}(OrderedDict{Symbol, AlgTerm}()))
#   end
# end

function AlgSort(c::Context, t::AlgTerm)
  # t_sub = substitute_funs(c, t)
  # if t_sub != t
  #   return AlgSort(c, t_sub)
  # end
  @match t begin
    Var(i) => begin
      binding = c[i]
      AlgSort(getvalue(binding))
    end
    Constant(_, oftype) => AlgSort(oftype)
    TermApp(method, args) => begin
      binding = c[method.method]
      value = getvalue(binding)
      AlgSort(value.type)
    end
    DotAccess(to, field) => begin
      parentsort = AlgSort(c, bodyof(bodyof(t)))
      if istuple(parentsort)
        parentsort.body.fields[headof(bodyof(t))]
      else
        algstruct = c[methodof(AlgSort(c, bodyof(bodyof(t))))] |> getvalue
        AlgSort(getvalue(algstruct.fields[headof(bodyof(t))]))
      end
    end
    Annot(_, type) => AlgSort(type)
    # NamedTupleTerm??
  end
end

function AlgSort(t::AlgType)
  @match t begin
    TypeApp(method, args) => PrimSort(method)
    TypeEq(sort, equands) => error("haven't refactored AlgEq yet")
    NamedTupleType(tuple) =>
      TupleSort(map(AlgSort, tuple))
  end
end

# function tcompose(t::AbstractDtry{AlgType})
#   @match t begin
#     Dtrys.Node(bs) =>
#       AlgType(AlgNamedTuple(OrderedDict(k => tcompose(v) for (k,v) in AbstractTrees.children(t))))
#     Dtrys.Leaf(v) => v
#     Dtrys.Empty() => AlgType(AlgNamedTuple(OrderedDict{Symbol, AlgType}()))
#   end
# end

# function Prims.getindex(a::AlgTerm, v::DtryVar)
#   @match v begin
#     Dtrys.Root() => a
#     Dtrys.Nested((n, v′)) => getindex(AlgTerm(AlgDot(n, a)), v′)
#   end
# end

# function Prims.getproperty(a::AlgTerm, n::Symbol)
#   AlgTerm(AlgDot(n, a))
# end

# # Type Contexts
# ###############

# const TypeCtx = Context{AlgType}

# """
# A type or term with an accompanying type context, e.g.

#  (a,b)::R        (a,b)::Ob
# -----------  or  ----------
#   a*(a+b)         Hom(a,b)
# """

# @struct_hash_equal struct InCtx{T}
#   ctx::TypeCtx
#   val::T
# end

# const TermInCtx = InCtx{AlgTerm}
# const TypeInCtx = InCtx{AlgType}

# Scopes.getvalue(i::InCtx) = i.val
# Scopes.getcontext(i::InCtx) = i.ctx


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
