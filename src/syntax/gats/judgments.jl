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

TypeScope(bindings::Vector{Binding{AlgType}}; tag=newscopetag()) = TypeScope(Scope(bindings; tag))
TypeScope(bindings::Pair{Symbol, AlgType}...) = TypeScope(Scope{AlgType}(bindings...))

Scopes.getscope(ts::TypeScope) = ts.scope

function Base.show(io::IO, ts::TypeScope)
  print(io, toexpr(EmptyContext{AlgType}(), ts))
end

"""
A GAT is conceptually a bunch of `Judgment`s strung together.
"""
abstract type Judgment <: HasContext{AlgType} end

abstract type TrmTypConstructor <: Judgment end

argsof(t::TrmTypConstructor) = t[t.args]

Scopes.getscope(t::TrmTypConstructor) = t.localcontext

Base.getindex(tc::TrmTypConstructor, lid::LID) = getindex(tc.localcontext, lid)

Base.getindex(tc::TrmTypConstructor, lids::AbstractVector{LID}) = getindex(tc.localcontext, lids)

"""
`AlgDeclaration`

A declaration of a constructor; constructor methods in the form of
`AlgTermConstructors` or the accessors for `AlgTypeConstructors` follow later in
the theory.

If `overloads` is nothing, this is declared in the theory module as a new function, i.e.

```julia
function foo end
```

If `overloads` is a vector of symbols, then this is imported into the theory module
from the fully-qualified module name given by the vector of symbols, i.e.

```julia
import Base: foo
```
"""
@struct_hash_equal struct AlgDeclaration <: Judgment
  overloads::Union{Nothing, Vector{Symbol}}
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

getdecl(tc::AlgTypeConstructor) = tc.declaration

"""
`AlgAccessor`

The arguments to a term constructor serve a dual function as both arguments and
also methods to extract the value of those arguments.

I.e., declaring `Hom(dom::Ob, codom::Ob)::TYPE` implicitly overloads a previous
declaration for `dom` and `codom`, or creates declarations if none previously
exist.
"""
@struct_hash_equal struct AlgAccessor <: Judgment
  declaration::Ident
  typecondecl::Ident
  typecon::Ident
  arg::Int
end

Scopes.getcontext(acc::AlgAccessor) = EmptyContext{AlgType}()

getdecl(acc::AlgAccessor) = acc.declaration

sortsignature(acc::AlgAccessor) = [AlgSort(acc.typecondecl, acc.typecon)]

"""
`AlgTermConstructor`

A declaration of a term constructor as a method of an `AlgFunction`.
"""
@struct_hash_equal struct AlgTermConstructor <: TrmTypConstructor
  declaration::Ident
  localcontext::TypeScope
  args::Vector{LID}
  type::AlgType
end

Scopes.getcontext(tc::AlgTermConstructor) = tc.localcontext

getdecl(tc::AlgTermConstructor) = tc.declaration

sortsignature(tc::Union{AlgTypeConstructor, AlgTermConstructor}) =
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
