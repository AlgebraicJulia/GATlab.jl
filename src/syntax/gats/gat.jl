"""
`GATSegment`

A piece of a GAT, consisting of a scope that binds judgments to names, possibly
disambiguated by argument sorts.

This is a struct rather than just a type alias so that we can customize the show method.
"""
@struct_hash_equal struct GATSegment <: HasScope{Judgment}
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
  if haskey(m.bysignature, sig)
    error("method already overloaded for signature: $sig")
  else
    m.bysignature[sig] = method
  end

function resolvemethod(m::MethodResolver, sig::AlgSorts)
  m.bysignature[sig]
end

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
@struct_hash_equal struct GAT <: HasScopeList{Judgment}
  name::Symbol
  segments::ScopeList{Judgment}
  resolvers::OrderedDict{Ident, MethodResolver}
  sorts::Vector{AlgSort}
  accessors::OrderedDict{Ident, Dict{Int, Ident}}
  axioms::Vector{Ident}
end

function Base.copy(theory::GAT; name=theory.name)
  GAT(
    name,
    copy(theory.segments),
    deepcopy(theory.resolvers),
    copy(theory.sorts),
    deepcopy(theory.accessors),
    copy(theory.axioms),
  )
end

function GAT(name::Symbol)
  GAT(
    name,
    ScopeList{Judgment}(),
    OrderedDict{Ident, MethodResolver}(),
    AlgSort[],
    OrderedDict{Ident, Dict{Int, Ident}}(),
    Ident[],
  )
end


# Mutators which should only be called during construction of a theory

function unsafe_newsegment!(theory::GAT)
  Scopes.unsafe_pushscope!(theory.segments, GATSegment())
end

function unsafe_updatecache!(theory::GAT, x::Ident, judgment::AlgDeclaration)
  theory.resolvers[x] = MethodResolver()
end

function unsafe_updatecache!(theory::GAT, x::Ident, judgment::AlgTermConstructor)
  addmethod!(theory.resolvers[getdecl(judgment)], sortsignature(judgment), x)
end

function unsafe_updatecache!(theory::GAT, x::Ident, judgment::AlgTypeConstructor)
  addmethod!(theory.resolvers[getdecl(judgment)], sortsignature(judgment), x)
  push!(theory.sorts, AlgSort(getdecl(judgment), x))
  theory.accessors[x] = Dict{Int, Ident}()
end

function unsafe_updatecache!(theory::GAT, x::Ident, judgment::AlgFunction)
  addmethod!(theory.resolvers[getdecl(judgment)], sortsignature(judgment), x)
end

function unsafe_updatecache!(theory::GAT, x::Ident, judgment::AlgStruct)
  addmethod!(theory.resolvers[getdecl(judgment)], sortsignature(judgment), x)
  addmethod!(theory.resolvers[getdecl(judgment)], typesortsignature(judgment), x) # Collision?
  push!(theory.sorts, AlgSort(getdecl(judgment), x))
  theory.accessors[x] = Dict{Int, Ident}()
end


function unsafe_updatecache!(theory::GAT, x::Ident, judgment::AlgAccessor)
  addmethod!(theory.resolvers[getdecl(judgment)], sortsignature(judgment), x)
  theory.accessors[judgment.typecon][judgment.arg] = x
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
    for line in block.args
      println(io, "  ", line)
    end
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
funsorts(theory::GAT) = [AlgSort(x...) for x in termcons(theory)]
allsorts(theory::GAT) = sorts(theory) ∪ funsorts(theory)

AlgSort(theory::GAT, s::Symbol) = only([x for x in allsorts(theory)
                                        if nameof(headof(x)) == s])

primitive_sorts(theory::GAT) = 
  filter(s->getvalue(theory[methodof(s)]) isa AlgTypeConstructor, sorts(theory))

# NOTE: AlgStruct is the only derived sort this returns.
struct_sorts(theory::GAT) = 
  filter(s->getvalue(theory[methodof(s)]) isa AlgStruct, sorts(theory))

function termcons(theory::GAT)
  xs = Tuple{Ident, Ident}[]
  for (decl, resolver) in theory.resolvers
    for (_, method) in allmethods(resolver)
      if getvalue(theory, method) isa AlgTermConstructor
        push!(xs, (decl, method))
      end
    end
  end
  xs
end

function typecons(theory::GAT)
  xs = Tuple{Ident, Ident}[]
  for (decl, resolver) in theory.resolvers
    for (_, method) in allmethods(resolver)
      if getvalue(theory, method) isa AlgTypeConstructor
        push!(xs, (decl, method))
      end
    end
  end
  xs
end

Base.issubset(t1::GAT, t2::GAT) =
  all(s->hastag(t2, s), gettag.(Scopes.getscopelist(t1).scopes))

Scopes.getcontext(theory::GAT, s::AlgSort) = getcontext(getvalue(theory[methodof(s)]))

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

gettheory(p::GATContext) = p.theory

gettypecontext(p::GATContext) = p.context

Scopes.getcontext(c::GATContext) = AppendContext(c.theory, c.context)

Scopes.AppendContext(c::GATContext, context::Context{AlgType}) =
  GATContext(c.theory, AppendContext(c.context, context))

function methodlookup(c::GATContext, x::Ident, sig::AlgSorts)
  theory = c.theory
  if haskey(theory.resolvers, x) && haskey(theory.resolvers[x].bysignature, sig)
    resolvemethod(theory.resolvers[x], sig)
  else
    error("no method of $x found with signature $(getdecl.(sig))")
  end
end

hasname!(theory::GAT, name::Symbol) = if hasname(theory, name)
  ident(theory; name)
else
  Scopes.unsafe_pushbinding!(theory, Binding{Judgment}(name, AlgDeclaration()))
end

"""Get all structs in a theory"""
structs(t::GAT) = AlgStruct[getvalue(t[methodof(s)]) for s in struct_sorts(t)]
