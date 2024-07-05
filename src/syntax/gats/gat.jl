using Markdown

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

function rename(tag::ScopeTag, renames::Dict{Symbol,Symbol}, segment::GATSegment)
  GATSegment(rename(tag, renames, segment.scope))
end

function reident(reps::Dict{Ident}, segment::GATSegment)
  GATSegment(reident(reps, segment.scope))
end

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

function rename(tag::ScopeTag, renames::Dict{Symbol,Symbol}, m::MethodResolver)
  MethodResolver(rename(tag, renames, m.bysignature))
end

function rename(tag::ScopeTag, renames::Dict{Symbol,Symbol}, bysignature::Dict{AlgSorts, Ident})
  if length(bysignature) == 0
    bysignature
  else
    merge(map(collect(bysignature)) do (algsorts, ident)
      Dict(rename(tag, renames, algsorts) => rename(tag, renames, ident))
    end...)
  end
end

function reident(reps::Dict{Ident, Ident}, key::Ident, m::MethodResolver)
  MethodResolver(reident(reps, key, m.bysignature))
end

function reident(reps::Dict{Ident}, key::Ident, bysignature::Dict{AlgSorts, Ident})
  if length(bysignature) == 0
    bysignature
  else
    merge(map(collect(bysignature)) do (algsorts, ident)
      @match algsorts begin
        [] => begin
          Dict(algsorts => reident(gettag(key), ident))
        end
        _  => Dict(reident.(Ref(reps), algsorts) => reident(reps, ident))
      end
    end...)
  end
end

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

Base.isempty(T::GAT) = T.name == :_EMPTY

# """ 
# `idents(T::GAT) : Vector{Ident}`

# """
# function idents(T::GAT)
#   Iterators.flatten(map(getidents.(T.segments.scopes)) do idents
#     filter(x -> !isnothing(x.name), idents)
#   end) |> collect
# end

function rename(tag::ScopeTag, renames::Dict{Symbol,Symbol}, gat::GAT)
  GAT(gat.name, rename(tag, renames, gat.segments), rename(tag, renames, gat.resolvers), rename(tag, renames, gat.sorts), gat.accessors, gat.axioms) 
end

function reident(reps::Dict{Ident}, gat::GAT)
  GAT(gat.name, 
      reident(reps, gat.segments),
      reident(reps, gat.resolvers),
      reident.(Ref(reps), gat.sorts),
      reident(reps, gat.accessors),
      reident.(Ref(reps), gat.axioms))
end

function rename(tag::ScopeTag, renames::Dict{Symbol, Symbol}, resolvers::OrderedDict{Ident, MethodResolver})
  if length(resolvers)==0
    resolvers
  else
    merge(map(collect(resolvers)) do (r,m)
      Dict(rename(tag, renames, r) => rename(tag, renames, m))
    end...)
  end
end

function reident(reps::Dict{Ident}, resolvers::OrderedDict{Ident, MethodResolver})
  if length(resolvers)==0
    resolvers
  else
    merge(map(collect(resolvers)) do (r, m)
      key = reident(reps, r)
      Dict(key => reident(reps, key, m))
      # Dict(reident(reps, r) => reident(reps, m)) # reident(reps, m)
    end...)
  end
end

function reident(reps::Dict{Ident}, d::Dict{Int64, Ident})
  if length(d) == 0
    d
  else
    merge(map(collect(d)) do (k, v)
      Dict(k => reident(reps, v))
    end...)
  end
end

function reident(reps::Dict{Ident}, accessors::OrderedDict{Ident, Dict{Int64, Ident}})
  if length(accessors) == 0
    accessors
  else
    merge(map(collect(accessors)) do (i, d)
      Dict(reident(reps, i) => reident(reps, d))
    end...)
  end
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
  push!(theory.sorts, PrimSort(ResolvedMethod(getdecl(judgment), x)))
  theory.accessors[x] = Dict{Int, Ident}()
end

function unsafe_updatecache!(theory::GAT, x::Ident, judgment::AlgFunction)
  addmethod!(theory.resolvers[getdecl(judgment)], sortsignature(judgment), x)
end

function unsafe_updatecache!(theory::GAT, x::Ident, judgment::AlgStruct)
  addmethod!(theory.resolvers[getdecl(judgment)], sortsignature(judgment), x)
  addmethod!(theory.resolvers[getdecl(judgment)], typesortsignature(judgment), x) # Collision?
  push!(theory.sorts, PrimSort(ResolvedMethod(getdecl(judgment), x)))
  theory.accessors[x] = Dict{Int, Ident}()
end


function unsafe_updatecache!(theory::GAT, x::Ident, judgment::AlgAccessor)
  # @info "AccessorC" getdecl(judgment) sortsignature(judgment) x
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

function unsafe_pushsegment!(theory::GAT, segment::GATSegment)
  Scopes.unsafe_pushscope!(theory.segments, segment)
  for (x, judgment) in identvalues(segment)
    # @info "What is being pushed" x judgment identvalues(segment) 
    unsafe_updatecache!(theory, x, judgment)
  end
  segment
end

# Pretty-printing

function Base.repr(theory::GAT)
  head = theory.name
  vec = []
  for seg in theory.segments.scopes
    push!(vec, LineNumberNode)
    block = toexpr(theory, seg)
    for line in block.args
      push!(vec, line, LineNumberNode)
    end
  end
  # Newlines in Markdown just require inserting a new line in the string.
  replace!(line -> line == LineNumberNode ? "
          " : line, vec)
  string = join(vec)
  Markdown.parse("""
  ## $head

  $string

  """)
end

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

declarations(t::GAT) = keys(t.resolvers)
