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

# TODO can we make this more elegant?
function reident(reps::Dict{Ident}, t::MethodApp{T}) where {T}
  head = reident(reps, t.head)
  MethodApp{T}(
    head,
    retag(Dict(t.head.tag => head.tag), t.method),
    reident.(Ref(reps), t.args)
  )
end

abstract type AlgAST end

bodyof(t::AlgAST) = t.body

"""
`AlgTerm`

One syntax tree to rule all the terms.
"""
@struct_hash_equal struct AlgTerm <: AlgAST
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

rename(tag::ScopeTag, reps::Dict{Symbol,Symbol}, t::AlgTerm) =
  AlgTerm(rename(tag, reps, t.body))

retag(reps::Dict{ScopeTag, ScopeTag}, t::AlgTerm) = AlgTerm(retag(reps, t.body))

reident(reps::Dict{Ident}, t::AlgTerm) =
  AlgTerm(reident(reps, t.body))

"""
`Eq`

The type of equality judgments.
"""
@struct_hash_equal struct Eq
  equands::Tuple{AlgTerm, AlgTerm}
end

retag(reps::Dict{ScopeTag, ScopeTag}, eq::Eq) = Eq(retag.(Ref(reps), eq.equands))

rename(tag::ScopeTag, reps::Dict{Symbol, Symbol}, eq::Eq) =
  Eq(retag.(Ref(tag), Ref(reps), eq.equands))

reident(reps::Dict{Ident}, eq::Eq) = Eq(reident.(Ref(reps), eq.equands))

"""
`AlgType`

One syntax tree to rule all the types.
"""
@struct_hash_equal struct AlgType <: AlgAST
  body::Union{MethodApp{AlgTerm}, Eq}
end

function AlgType(fun::Ident, method::Ident)
  AlgType(MethodApp{AlgTerm}(fun, method, EMPTY_ARGS))
end

bodyof(t::AlgType) = t.body

isvariable(t::AlgType) = false

isapp(t::AlgType) = t.body isa MethodApp

iseq(t::AlgType) = t.body isa Eq

isconstant(t::AlgType) = false

AlgType(head::Ident, method::Ident, args::Vector{AlgTerm}) =
  AlgType(MethodApp{AlgTerm}(head, method, args))

AlgType(lhs::AlgTerm, rhs::AlgTerm) =
  AlgType(Eq((lhs, rhs)))

retag(reps::Dict{ScopeTag,ScopeTag}, t::AlgType) =
  AlgType(retag(reps, t.body))

rename(tag::ScopeTag, reps::Dict{Symbol, Symbol}, t::AlgType) =
  AlgType(rename(tag, reps, t.body))

function reident(reps::Dict{Ident}, t::AlgType)
  AlgType(reident(reps, t.body))
end

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
"""
@struct_hash_equal struct AlgSort
  head::Ident
  method::Ident
end

AlgSort(t::AlgType) = AlgSort(t.body.head, t.body.method)

headof(a::AlgSort) = a.head
methodof(a::AlgSort) = a.method

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

Base.nameof(sort::AlgSort) = nameof(sort.head)

getdecl(s::AlgSort) = s.head

function reident(reps::Dict{Ident}, a::AlgSort)
  newhead = reident(reps, a.head)
  newmethod = retag(Dict(a.head.tag => newhead.tag), a.method)
  AlgSort(newhead, newmethod) 
  # AlgSort(reident(reps, a.head), reident(reps, a.method))
  # TODO the method should just inherit the tag in the head?
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
