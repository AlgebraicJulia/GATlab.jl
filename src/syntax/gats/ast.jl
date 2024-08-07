# GAT ASTs
##########


# AlgSorts
#---------
abstract type AbstractAlgSort end

"""
`AlgSort`

A *sort*, which is essentially a type constructor without arguments
"""
@struct_hash_equal struct AlgSort <: AbstractAlgSort
  head::Ident
  method::Ident
end

function reident(reps::Dict{Ident}, a::AlgSort)
  newhead = reident(reps, headof(a))
  newmethod = retag(Dict(a.head.tag => newhead.tag), methodof(a))
  AlgSort(newhead, newmethod) 
end

"""
`AlgSort`

A sort for equality judgments of terms for a particular sort
"""
@struct_hash_equal struct AlgEqSort <: AbstractAlgSort
  head::Ident
  method::Ident
end

iseq(::AlgEqSort) = true
iseq(::AlgSort) = false
headof(a::AbstractAlgSort) = a.head
methodof(a::AbstractAlgSort) = a.method

Base.nameof(sort::AbstractAlgSort) = nameof(sort.head)

getdecl(s::AbstractAlgSort) = s.head

function reident(reps::Dict{Ident}, a::AlgEqSort)
  newhead = reident(reps, headof(a))
  newmethod = retag(Dict(a.head.tag => newhead.tag), methodof(a))
  AlgEqSort(newhead, newmethod) 
end


"""
We need this to resolve a mutual reference loop; the only subtype is Constant
"""
abstract type AbstractConstant end

"""
We need this to resolve a mutual reference loop; the only subtype is Dot
"""
abstract type AbstractDot end

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
  body::Union{Ident, MethodApp{AlgTerm}, AbstractConstant, AbstractDot}
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

isdot(t::AlgAST) = t.body isa AlgDot

isconstant(t::AlgTerm) = t.body isa AbstractConstant

rename(tag::ScopeTag, reps::Dict{Symbol,Symbol}, t::AlgTerm) =
  AlgTerm(rename(tag, reps, t.body))

retag(reps::Dict{ScopeTag, ScopeTag}, t::AlgTerm) = AlgTerm(retag(reps, t.body))

reident(reps::Dict{Ident}, t::AlgTerm) = AlgTerm(reident(reps, t.body))

function AlgSort(c::Context, t::AlgTerm)
  t_sub = substitute_funs(c, t)
  if t_sub != t 
    return AlgSort(c, t_sub)
  end
  if isconstant(t)
    AlgSort(t.body.type)
  elseif isapp(t)
    binding = c[t.body.method]
    value = getvalue(binding)
    AlgSort(value.type)
  elseif isdot(t)
    algstruct = c[AlgSort(c, bodyof(bodyof(t))).method] |> getvalue
    AlgSort(getvalue(algstruct.fields[headof(bodyof(t))]))
  else # variable
    binding = c[t.body]
    AlgSort(getvalue(binding))
  end
end

"""
`Eq`

The type of equality judgments.
"""
@struct_hash_equal struct Eq
  equands::Tuple{AlgTerm, AlgTerm}
  sort::AlgSort
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

AlgType(c::Context, lhs::AlgTerm, rhs::AlgTerm) =
  AlgType(Eq((lhs, rhs), AlgSort(c, lhs)))

retag(reps::Dict{ScopeTag,ScopeTag}, t::AlgType) =
  AlgType(retag(reps, t.body))

rename(tag::ScopeTag, reps::Dict{Symbol, Symbol}, t::AlgType) =
  AlgType(rename(tag, reps, t.body))

function reident(reps::Dict{Ident}, t::AlgType)
  AlgType(reident(reps, t.body))
end

AlgSort(t::AlgType) = if iseq(t)
  AlgEqSort(t.body.sort.head, t.body.sort.method)
else 
  AlgSort(t.body.head, t.body.method)
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


"""
Accessing a name from a term of tuple type
"""
@struct_hash_equal struct AlgDot <: AbstractDot
  head::Ident
  body::AlgTerm
end

headof(a::AlgDot) = a.head 
bodyof(a::AlgDot) = a.body

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
