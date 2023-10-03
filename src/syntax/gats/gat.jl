"""
`GATSegment`

A piece of a GAT, consisting of a scope that binds judgments to names, possibly
disambiguated by argument sorts.

This is a struct rather than just a type alias so that we can customize the show method.
"""
struct GATSegment <: HasScope{Judgment}
  scope::Scope{Judgment}
end

GATSegment() = GATSegment(Scope{Judgment}())

Scopes.getscope(seg::GATSegment) = seg.scope

"""
`MethodResolver`

Right now, this just maps a sort signature to the resolved method.

When we eventually support varargs, this will have to do something slightly
fancier.
"""
@struct_hash_equal struct MethodResolver
  bysignature::Dict{AlgSorts, Ident}
end

function MethodResolver()
  MethodResolver(Dict{AlgSorts, Ident}())
end

addmethod!(m::MethodResolver, sig::AlgSorts, method::Ident) =
  m.bysignature[sig] = method

resolvemethod(m::MethodResolver, sig::AlgSorts) = m.bysignature[sig]

allmethods(m::MethodResolver) = pairs(m.bysignature)

"""
`GAT`

A generalized algebraic theory. Essentially, just consists of a name and a list
of `GATSegment`s, but there is also some caching to make access faster.
Specifically, there is a dictionary to map ScopeTag to position in the list of
segments, and there are lists of all of the identifiers for term constructors,
type constructors, and axioms so that they can be iterated through faster.

GATs allow overloading but not shadowing.
"""
struct GAT <: HasScopeList{Judgment}
  name::Symbol
  segments::ScopeList{Judgment}
  resolvers::Dict{Ident, MethodResolver}
  sorts::Vector{AlgSort}
  axioms::Vector{Ident}
end

function Base.copy(theory::GAT; name=theory.name)
  GAT(
    name,
    copy(theory.segments),
    deepcopy(theory.resolvers),
    copy(theory.sorts),
    copy(theory.axioms)
  )
end

function GAT(name::Symbol)
  GAT(
    name,
    ScopeList{Judgment}(),
    Dict{Ident, MethodResolver}(),
    AlgSort[],
    Ident[]
  )
end

# Mutators which should only be called during construction of a theory

function unsafe_newsegment!(theory::GAT)
  Scopes.unsafe_pushscope!(theory.segments, GATSegment())
end

function unsafe_updatecache!(theory::GAT, x::Ident, judgment::AlgDeclaration)
  theory.resolvers[x] = MethodResolver()
end

function unsafe_updatecache!(
  theory::GAT,
  x::Ident,
  judgment::Union{AlgTermConstructor, AlgAccessor}
)
  addmethod!(theory.resolvers[getdecl(judgment)], sortsignature(judgment), x)
end

function unsafe_updatecache!(theory::GAT, x::Ident, judgment::AlgTypeConstructor)
  addmethod!(theory.resolvers[getdecl(judgment)], sortsignature(judgment), x)
  push!(theory.sorts, AlgSort(getdecl(judgment), x))
end

function unsafe_updatecache!(theory::GAT, x::Ident, judgment::AlgAxiom)
  push!(theory.axioms, x)
end

function unsafe_updatecache!(theory::GAT, x::Ident, judgment::Alias)
  nothing
end

function Scopes.unsafe_pushbinding!(theory::GAT, binding::Binding{Judgment})
  x = Scopes.unsafe_pushbinding!(theory.segments, binding)
  unsafe_updatecache!(theory, x, getvalue(binding))
  x
end

# Pretty-printing

function Base.show(io::IO, theory::GAT)
  println(io, "GAT(", theory.name, "):")
  for seg in theory.segments.scopes
    block = toexpr(theory, seg)
    for line in block.args[1:end-1]
      println(io, "  ", line)
    end
    print(io, "  ", block.args[end])
  end
end

# Accessors

Base.nameof(theory::GAT) = theory.name

resolvers(theory::GAT) = theory.resolvers

Scopes.getscopelist(c::GAT) = c.segments

function allnames(theory::GAT; aliases=false)
  filter(!=(nothing), nameof.(getidents(theory; aliases)))
end

sorts(theory::GAT) = theory.sorts

Base.issubset(t1::GAT, t2::GAT) =
  all(s->hastag(t2, s), gettag.(Scopes.getscopelist(t1).scopes))

"""
`GATContext`

A context consisting of two parts: a GAT and a TypeCtx

Certain types (like AlgTerm) can only be parsed in a GATContext, because
they require access to the method resolving in the GAT.
"""
struct GATContext <: HasContext{Union{Judgment, AlgType}}
  theory::GAT
  context::Context{AlgType}
end

GATContext(theory::GAT) = GATContext(theory, EmptyContext{AlgType}())

Scopes.getcontext(c::GATContext) = AppendContext(c.theory, c.context)

Scopes.AppendContext(c::GATContext, context::Context{AlgType}) =
  GATContext(c.theory, AppendContext(c.context, context))

function methodlookup(c::GATContext, decl::Ident, sig::AlgSorts)
  resolvemethod(c.theory.resolvers[decl], sig)
end