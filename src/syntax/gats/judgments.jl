# GAT Judgments
###############

"""
`TypeScope`

A scope where variables are assigned to `AlgType`s. We use a wrapper
here so that it pretty prints as `[a::B]` instead of `{a => AlgType(B)}`
"""
struct TypeScope <: HasScope{AlgType}
  scope::Scope{AlgType}
end

TypeScope() = TypeScope(Scope{AlgType}())
TypeScope(t::TypeScope) = t

TypeScope(bindings::Vector{Binding{AlgType}}; tag=newscopetag()) = TypeScope(Scope(bindings; tag))
TypeScope(bindings::Pair{Symbol, AlgType}...) = TypeScope(Scope{AlgType}(bindings...))

Scopes.getscope(ts::TypeScope) = ts.scope
Scopes.unsafe_pushbinding!(ts::TypeScope, b) = 
  Scopes.unsafe_pushbinding!(ts.scope, b)

function Base.show(io::IO, ts::TypeScope)
  print(io, toexpr(EmptyContext{AlgType}(), ts))
end


"""
A type that comes from applying a term constructor (which has a tuple output)

We don't always know what the inputs to that function were. E.g. 

universal(p::pushout[apex::Ob, i1::b->apex, i2::c->apex], ...) 
  ⊣ [(a,b,c):Ob, ...]

However, because of the possibility of overloading, we need to know what the 
argument sorts are in order to identify the method.
"""
@struct_hash_equal struct AlgTup <: AbstractAlgTup
  head::Ident
  method::Ident
  body::TypeScope
end
  
bodyof(t::AlgTup) = t.body
methodof(t::AlgTup) = t.method
headof(t::AlgTup) = t.head

"""
A GAT is conceptually a bunch of `Judgment`s strung together.
"""
abstract type Judgment <: HasContext{AlgType} end

abstract type TrmTypConstructor <: Judgment end

argsof(t::TrmTypConstructor) = t[t.args]

Scopes.getscope(t::TrmTypConstructor) = t.localcontext

Base.getindex(tc::TrmTypConstructor, lid::LID) = getindex(tc.localcontext, lid)

Base.getindex(tc::TrmTypConstructor, lids::AbstractVector{LID}) = getindex(tc.localcontext, lids)

getdecl(tc::TrmTypConstructor) = tc.declaration

"""
`AlgDeclaration`

A declaration of a constructor; constructor methods in the form of
`AlgTermConstructors` or the accessors for `AlgTypeConstructors` follow later in
the theory.
"""
@struct_hash_equal struct AlgDeclaration <: Judgment
end

Scopes.getcontext(::AlgDeclaration) = EmptyContext{AlgType}()

"""
`AlgTypeConstructor`

A declaration of a type constructor.
"""
@struct_hash_equal struct AlgTypeConstructor <: TrmTypConstructor
  declaration::Ident
  localcontext::TypeScope
  args::Vector{LID}
end

Scopes.getcontext(tc::AlgTypeConstructor) = tc.localcontext

abstract type AccessorField <: Judgment end

"""
`AlgAccessor`

The arguments to a term constructor serve a dual function as both arguments and
also methods to extract the value of those arguments.

I.e., declaring `Hom(dom::Ob, codom::Ob)::TYPE` implicitly overloads a previous
declaration for `dom` and `codom`, or creates declarations if none previously
exist.
"""
@struct_hash_equal struct AlgAccessor <: AccessorField
  declaration::Ident
  typecondecl::Ident
  typecon::Ident
  arg::Int
end

Scopes.getcontext(::AccessorField) = EmptyContext{AlgType}()

getdecl(acc::AccessorField) = acc.declaration

sortsignature(acc::AccessorField) = [AlgSort(acc.typecondecl, acc.typecon)]


"""
`AlgTermConstructor`

A declaration of a term constructor as a method of an `AlgFunction`.
"""
@struct_hash_equal struct AlgTermConstructor <: TrmTypConstructor
  declaration::Ident
  localcontext::TypeScope
  args::Vector{LID}
  type::Union{TypeScope,AlgType}
end

Scopes.getcontext(tc::AlgTermConstructor) = tc.localcontext

sortsignature(tc::TrmTypConstructor) =
  AlgSort.(getvalue.(argsof(tc)))

"""
`AlgAxiom`

A declaration of an axiom
"""
@struct_hash_equal struct AlgAxiom <: Judgment
  localcontext::TypeScope
  sort::AlgSort
  equands::Vector{AlgTerm}
end

Scopes.getcontext(t::AlgAxiom) = t.localcontext

"""
`AlgSorts`

A description of the argument sorts for a term constructor, used to disambiguate
multiple term constructors of the same name.
"""
const AlgSorts = Vector{AlgSort}

"""
`AlgStruct`

A declaration which is sugar for an AlgTypeConstructor, an AlgTermConstructor 
which constructs an element of that type, and projection term constructors. E.g.

    struct Cospan(dom, codom) ⊣ [dom:Ob, codom::Ob]
      apex::Ob
      i1::dom->apex
      i2::codom->apex
    end

Is sugar for:

    Cospan(dom, codom, apex, i1, i2)::TYPE 
      ⊣ [(dom, codom, apex)::Ob, i1::dom->apex, i2::codom->apex]

    Cospan(apex, i1, i2)::Cospan(dom, codom, apex, i1, i2) 
      ⊣ [(dom, codom, apex)::Ob, i1::dom->apex, i2::codom->apex]

    apex(csp::Cospan(d, c, a, i_1, i_2))::Ob             ⊣ [(d,c,a)::Ob, ...]
    i1(csp  ::Cospan(d, c, a, i_1, i_2))::(d->apex(csp)) ⊣ [(d,c,a)::Ob, ...]
    i2(csp  ::Cospan(d, c, a, i_1, i_2))::(c->apex(csp)) ⊣ [(d,c,a)::Ob, ...]

    apex(Cospan(a,i_1,i_2)) == a ⊣ [a::Ob,...]
    i1(Cospan(a,i_1,i_2)) == i_1 ⊣ [a::Ob,...]
    i2(Cospan(a,i_1,i_2)) == i_2 ⊣ [a::Ob,...]

    c == Cospan(apex(c), i1(c), i2(c)) ⊣ [..., c::Cospan(...)]

"""
@struct_hash_equal struct AlgStruct <: TrmTypConstructor
  declaration::Ident
  localcontext::TypeScope
  typeargs::Vector{LID}
  args::Vector{LID}
end

Base.nameof(t::AlgStruct) = nameof(t.declaration)
typeargsof(t::AlgStruct) = t[t.typeargs]
typesortsignature(tc::AlgStruct) =
  AlgSort.(getvalue.(typeargsof(tc)))

Scopes.getcontext(tc::AlgStruct) = tc.localcontext

"""
A shorthand for a function, such as "square(x) := x * x".  It is relevant for 
models but can be ignored by theory maps, as it is fully determined by other 
judgments in the theory.
"""
@struct_hash_equal struct AlgFunction <: TrmTypConstructor
  declaration::Ident
  localcontext::TypeScope
  args::Vector{LID}
  value::AlgTerm
end

Scopes.getcontext(tc::AlgFunction) = tc.localcontext
