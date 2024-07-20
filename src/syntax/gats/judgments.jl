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

rename(tag::ScopeTag, renames::Dict{Symbol,Symbol}, t::TypeScope ) = TypeScope(rename(tag, renames, t.scope))

reident(reps::Dict{Ident}, t::TypeScope) = TypeScope(reident(reps, t.scope))

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

reident(reps::Dict{Ident}, a::AlgDeclaration) = a

"""
`AlgTypeConstructor`

A declaration of a type constructor.
"""
@struct_hash_equal struct AlgTypeConstructor <: TrmTypConstructor
  declaration::Ident
  localcontext::TypeScope
  args::Vector{LID}
end

Scopes.getcontext(tc::TrmTypConstructor) = tc.localcontext

abstract type AccessorField <: Judgment end

rename(tag::ScopeTag, renames::Dict{Symbol,Symbol},tc::AlgTypeConstructor) = 
AlgTypeConstructor(tc.declaration, rename(tag, renames, tc.localcontext), tc.args)

reident(reps::Dict{Ident}, tc::AlgTypeConstructor) =
AlgTypeConstructor(reident(reps, tc.declaration), reident(reps, tc.localcontext), tc.args)

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


getdecl(acc::AccessorField) = acc.declaration

sortsignature(acc::AccessorField) = [PrimSort(ResolvedMethod(acc.typecondecl, acc.typecon))]


rename(tag::ScopeTag, renames::Dict{Symbol,Symbol}, a::AlgAccessor) = 
AlgAccessor(rename(tag, renames, a.declaration), rename(tag, renames, a.typecondecl), rename(tag, renames, a.typecon), a.arg)

reident(reps::Dict{Ident}, a::AlgAccessor) = 
AlgAccessor(reident(reps, a.declaration), reident(reps, a.typecondecl), reident(reps, a.typecon), a.arg)

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


sortsignature(tc::TrmTypConstructor) =
  AlgSort.(getvalue.(argsof(tc)))

function rename(tag::ScopeTag, renames::Dict{Symbol,Symbol}, term::AlgTermConstructor)
  AlgTermConstructor(rename(tag, renames, term.declaration),rename(tag, renames, term.localcontext),term.args,rename(tag, renames, term.type))
end

function reident(reps::Dict{Ident}, term::AlgTermConstructor)
  AlgTermConstructor(reident(reps, term.declaration),
                     reident(reps, term.localcontext),
                     term.args,
                     reident(reps, term.type))
end

"""
`AlgAxiom`

A declaration of an axiom
"""
@struct_hash_equal struct AlgAxiom <: Judgment
  localcontext::TypeScope
  sort::AlgSort
  equands::Vector{AlgTerm}
end


rename(tag::ScopeTag, renames::Dict{Symbol,Symbol}, t::AlgAxiom) = 
AlgAxiom(rename(tag, renames, t.localcontext), rename(tag, renames, t.sort), rename(tag, renames, t.equands))

function reident(reps::Dict{Ident}, a::AlgAxiom)
  AlgAxiom(reident(reps, a.localcontext), reident(reps, a.sort), reident.(Ref(reps), a.equands))
end

"""
`AlgSorts`

A description of the argument sorts for a term constructor, used to disambiguate
multiple term constructors of the same name.
"""

# rename(tag::ScopeTag, renames::Dict{Symbol,Symbol}, ts::Vector{AlgSort}) = map(ts) do t
#   AlgSort

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

Is tantamount to (in a vanilla GAT):

    Cospan(dom::Ob, codom::Ob)::TYPE 

    cospan(apex, i1, i2)::Cospan(dom, codom) 
      ⊣ [(dom, codom, apex)::Ob, i1::dom->apex, i2::codom->apex]

    apex(csp::Cospan(d::Ob, c::Ob))::Ob            
    i1(csp::Cospan(d::Ob, c::Ob))::(d->apex(csp))
    i2(csp::Cospan(d::Ob, c::Ob))::(c->apex(csp))

    apex(cospan(a, i_1, i_2)) == a  
      ⊣ [(dom, codom, apex)::Ob, i_1::dom->apex, i_2::codom->apex]
    i1(cospan(a, i_1, i_2)) == i_1 
      ⊣ [(dom, codom, apex)::Ob, i_1::dom->apex, i_2::codom->apex]
    i2(cospan(a, i_1, i_2)) == i_2
      ⊣ [(dom, codom, apex)::Ob, i_1::dom->apex, i_2::codom->apex]

    cospan(apex(csp), i1(csp), i2(csp)) == csp
      ⊣ [(dom, codom)::Ob, csp::Cospan(dom, codom)]

"""
@struct_hash_equal struct AlgStruct <: TrmTypConstructor
  declaration::Ident
  localcontext::TypeScope
  typeargs::Vector{LID}
  fields::TypeScope
end

Base.nameof(t::AlgStruct) = nameof(t.declaration)
typeargsof(t::AlgStruct) = t[t.typeargs]
typesortsignature(tc::AlgStruct) =
  AlgSort.(getvalue.(typeargsof(tc)))
argsof(t::AlgStruct) = getbindings(t.fields)

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
