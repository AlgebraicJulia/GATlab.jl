# GAT ASTs
##########

"""
We need this to resolve a mutual reference loop; the only subtype is Constant
"""
abstract type AbstractConstant end

"""
`MethodApp`

An application of a method of a constructor to arguments. We need a type parameter
`T` because `AlgTerm` hasn't been defined yet, but the only type used for `T` will
in fact be `AlgTerm`.

`method` either points to an `AlgTermConstructor`, an `AlgTypeConstructor` or an
`AlgAccessor`,
"""
@struct_hash_equal struct MethodApp{T}
  head::Ident
  method::Ident
  args::Vector{T}
end

headof(t::MethodApp) = t.head
methodof(t::MethodApp) = t.method
argsof(t::MethodApp) = t.args

rename(tag::ScopeTag, reps::Dict{Symbol, Symbol}, t::MethodApp{T}) where {T} =
  MethodApp{T}(
    rename(tag, reps, t.head),
    rename(tag, reps, t.method),
    rename.(Ref(tag), Ref(reps), t.args)
  )

retag(reps::Dict{ScopeTag, ScopeTag}, t::MethodApp{T}) where {T} =
  MethodApp{T}(
    retag(reps, t.head),
    retag(reps, t.method),
    retag.(Ref(reps), t.args)
  )

"""
`AlgTerm`

One syntax tree to rule all the terms.
"""
@struct_hash_equal struct AlgTerm
  body::Union{Ident, MethodApp{AlgTerm}, AbstractConstant}
  function AlgTerm(body::Union{Ident, MethodApp{AlgTerm}, AbstractConstant})
    new(body)
  end
end

const EMPTY_ARGS = AlgTerm[]

function AlgTerm(fun::Ident, method::Ident, args::Vector{AlgTerm})
  AlgTerm(MethodApp{AlgTerm}(fun, method, args))
end

function AlgTerm(fun::Ident, method::Ident)
  AlgTerm(MethodApp{AlgTerm}(fun, method, EMPTY_ARGS))
end

isvariable(t::AlgTerm) = t.body isa Ident

isapp(t::AlgTerm) = t.body isa MethodApp

isconstant(t::AlgTerm) = t.body isa AbstractConstant

rename(tag::ScopeTag, reps::Dict{Symbol,Symbol}, t::AlgTerm) = AlgTerm(rename(tag, reps, t.body))

retag(reps::Dict{ScopeTag, ScopeTag}, t::AlgTerm) = AlgTerm(retag(reps, t.body))

"""
`AlgType`

One syntax tree to rule all the types.
`head` must be reference to a `AlgTypeConstructor`
"""
@struct_hash_equal struct AlgType
  body::MethodApp{AlgTerm}
end

isvariable(t::AlgType) = false

isapp(t::AlgType) = true

isconstant(t::AlgType) = false

AlgType(head::Ident, method::Ident, args::Vector{AlgTerm}) =
  AlgType(MethodApp{AlgTerm}(head, method, args))

retag(reps::Dict{ScopeTag,ScopeTag}, t::AlgType) =
  AlgType(retag(reps, t.body))

rename(tag::ScopeTag, reps::Dict{Symbol, Symbol}, t::AlgType) =
  AlgType(rename(tag, reps, t.body))

"""
Common methods for AlgType and AlgTerm
"""
function Base.show(io::IO, trm::T) where T<:Union{AlgTerm, AlgType}
  print(io, "$(nameof(T))(")
  print(io, toexpr(TypeScope(), trm))
  print(io, ")")
end

"""
`Constant`

A Julia value in an algebraic context. Type checked elsewhere.
"""
@struct_hash_equal struct Constant <: AbstractConstant
  value::Any
  type::AlgType
end

# AlgSorts
##########

"""
`AlgSort`

A *sort*, which is essentially a type constructor without arguments
`ref` must be reference to a `AlgTypeConstructor`
"""
@struct_hash_equal struct AlgSort
  head::Ident
  method::Ident
end

AlgSort(t::AlgType) = AlgSort(t.body.head, t.body.method)

function AlgSort(c::Context, t::AlgTerm)
  if isconstant(t)
    AlgSort(t.body.type)
  elseif isapp(t)
    binding = c[t.body.method]
    value = getvalue(binding)
    AlgSort(value.type)
  else # variable
    binding = c[t.body]
    AlgSort(getvalue(binding))
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