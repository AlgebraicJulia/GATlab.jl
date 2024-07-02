# GAT ASTs
##########

@struct_hash_equal struct AlgNamedTuple{T}
  fields::OrderedDict{Symbol, T}
end

# AlgSorts
#---------
abstract type AbstractAlgSort end

"""
`AlgSort`

A *sort*, which is essentially a type constructor without arguments
"""
@struct_hash_equal struct AlgSort <: AbstractAlgSort
  body::Union{Tuple{Ident, Ident}, AlgNamedTuple{AlgSort}}
end

function reident(reps::Dict{Ident}, a::AlgSort)
  newhead = reident(reps, headof(a))
  newmethod = retag(Dict(a.head.tag => newhead.tag), methodof(a))
  AlgSort(newhead, newmethod) 
end

AlgSort(head::Ident, method::Ident) = AlgSort((head, method))

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
istuple(s::AlgSort) = s.body isa AlgNamedTuple
headof(a::AbstractAlgSort) = a.body[1]
methodof(a::AbstractAlgSort) = a.body[2]

Base.nameof(sort::AbstractAlgSort) = nameof(headof(sort))

getdecl(s::AbstractAlgSort) = headof(s)

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

abstract type AbstractAlgAnnot end

"""
`AlgTerm`

One syntax tree to rule all the terms.
"""
@struct_hash_equal struct AlgTerm <: AlgAST
  body::Union{
    Ident,
    MethodApp{AlgTerm},
    AbstractConstant,
    AbstractDot,
    AbstractAlgAnnot,
    AlgNamedTuple{AlgTerm}
  }
end


const EMPTY_ARGS = AlgTerm[]

function AlgTerm(fun::Ident, method::Ident, args::Vector{AlgTerm})
  AlgTerm(MethodApp{AlgTerm}(fun, method, args))
end

function AlgTerm(fun::Ident, method::Ident)
  AlgTerm(MethodApp{AlgTerm}(fun, method, EMPTY_ARGS))
end

AlgTerm(t::AlgTerm) = t

function AlgTerm(tup::NamedTuple)
  AlgTerm(AlgNamedTuple{AlgTerm}(OrderedDict{Symbol, AlgTerm}(n => AlgTerm(v) for (n, v) in pairs(tup))))
end

isvariable(t::AlgTerm) = t.body isa Ident

isapp(t::AlgTerm) = t.body isa MethodApp

istuple(t::AlgTerm) = t.body isa AlgNamedTuple

isdot(t::AlgAST) = t.body isa AlgDot

isconstant(t::AlgTerm) = t.body isa AbstractConstant

rename(tag::ScopeTag, reps::Dict{Symbol,Symbol}, t::AlgTerm) =
  AlgTerm(rename(tag, reps, t.body))

retag(reps::Dict{ScopeTag, ScopeTag}, t::AlgTerm) = AlgTerm(retag(reps, t.body))

reident(reps::Dict{Ident}, t::AlgTerm) = AlgTerm(reident(reps, t.body))

function tcompose(t::AbstractTrie{AlgTerm})
  @match t begin
    Tries.Leaf(v) => v
    Tries.Node(bs) => 
      AlgTerm(AlgNamedTuple{AlgTerm}(OrderedDict{Symbol, AlgTerm}(
        (n, tcompose(v)) for (n, v) in bs
      )))
    Tries.Empty() =>
      AlgTerm(AlgNamedTuple{AlgTerm}(OrderedDict{Symbol, AlgTerm}()))
  end
end

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
    parentsort = AlgSort(c, bodyof(bodyof(t)))
    if istuple(parentsort)
      parentsort.body.fields[headof(bodyof(t))]
    else
      algstruct = c[methodof(AlgSort(c, bodyof(bodyof(t))))] |> getvalue
      AlgSort(getvalue(algstruct.fields[headof(bodyof(t))]))
    end
  elseif isannot(t)
    AlgSort(t.body.type)
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
  body::Union{MethodApp{AlgTerm}, Eq, AlgNamedTuple{AlgType}}
end

function AlgType(fun::Ident, method::Ident)
  AlgType(MethodApp{AlgTerm}(fun, method, EMPTY_ARGS))
end

bodyof(t::AlgType) = t.body

isvariable(t::AlgType) = false

isapp(t::AlgType) = t.body isa MethodApp

iseq(t::AlgType) = t.body isa Eq

istuple(t::AlgType) = t.body isa AlgNamedTuple

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

function AlgSort(t::AlgType)
  if iseq(t)
    AlgEqSort(headof(t.body.sort), methodof(t.body.sort))
  elseif istuple(t)
    AlgSort(AlgNamedTuple{AlgSort}(OrderedDict{Symbol, AlgSort}(k => AlgSort(v) for (k, v) in t.body.fields)))
  else 
    AlgSort(headof(t.body), methodof(t.body))
  end
end

function tcompose(t::AbstractTrie{AlgType})
  @match t begin
    Tries.Node(bs) =>
      AlgType(AlgNamedTuple(OrderedDict(k => tcompose(v) for (k,v) in AbstractTrees.children(t))))
    Tries.Leaf(v) => v
    Tries.Empty() => AlgType(AlgNamedTuple(OrderedDict{Symbol, AlgType}()))
  end
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
An explicitly type-annotated value.
"""
@struct_hash_equal struct AlgAnnot <: AbstractAlgAnnot
  term::AlgTerm
  type::AlgType
end

isannot(t::AlgTerm) = t.body isa AbstractAlgAnnot

"""
Accessing a name from a term of tuple type
"""
@struct_hash_equal struct AlgDot <: AbstractDot
  head::Symbol
  body::AlgTerm
  function AlgDot(head::Symbol, body::AlgTerm)
    if istuple(body)
      body.body.fields[head]
    else
      new(head, body)
    end
  end
end

headof(a::AlgDot) = a.head 
bodyof(a::AlgDot) = a.body

function Base.getindex(a::AlgTerm, v::TrieVar)
  @match v begin
    Tries.Root() => a
    Tries.Nested((n, v′)) => getindex(AlgTerm(AlgDot(n, a)), v′)
  end
end

function Base.getproperty(a::AlgTerm, n::Symbol)
  if n == :body
    # this is a hack: we should instead replace everywhere we use t.body
    # with `getbody(t)` or something like it
    getfield(a, :body)
  else
    AlgTerm(AlgDot(n, a))
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
