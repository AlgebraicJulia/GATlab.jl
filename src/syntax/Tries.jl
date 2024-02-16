module Tries
export Trie, PACKAGE_ROOT, ■, TrieVar, mapwithkey

using AbstractTrees
using OrderedCollections

struct TrieNode{X}
  branches::OrderedDict{Symbol, X}
end

struct TrieLeaf{A}
  value::A
end

struct Trie{A}
  content::Union{TrieLeaf{A}, TrieNode{Trie{A}}}
end

value(p::Trie) = content(p).value
branches(p::Trie) = content(p).branches
content(p::Trie) = getfield(p, :content)
isleaf(p::Trie) = content(p) isa TrieLeaf
leaf(x::A) where {A} = Trie{A}(TrieLeaf{A}(x))
isnode(p::Trie) = content(p) isa TrieNode
node(d::OrderedDict{Symbol, Trie{A}}) where {A} = Trie{A}(TrieNode{Trie{A}}(d))
node(ps::Pair{Symbol, Trie{A}}...) where {A} = node(OrderedDict{Symbol, Trie{A}}(ps...))
node(g::Base.Generator) = node(OrderedDict(g))

struct TrieIndexError <: Exception
  package::Trie
  key::Symbol
end

struct TrieDerefError <: Exception
  package::Trie
end

function Base.getproperty(p::Trie{A}, n::Symbol)::Trie{A} where {A}
  if isnode(p)
    d = branches(p)
    if haskey(d, n)
      d[n]
    else
      throw(TrieIndexError(p, n))
    end
  else
    throw(TrieIndexError(p, n))
  end
end

function Base.filter(f, t::Trie{A}) where {A}
  if isleaf(t)
    if f(t[])
      t
    else
      nothing
    end
  else
    branches′ = OrderedDict{Symbol, Trie{A}}()
    for (n, s) in branches(t)
      s′ = filter(f, s)
      if !isnothing(s′)
        branches′[n] = s′
      end
    end
    if length(branches′) > 0
      node(branches′)
    else
      nothing
    end
  end
end

function filtermap(f, t::Trie)
  if isleaf(t)
    v′ = f(t[])
    if !isnothing(v′)
      leaf(v′)
    end
  else
    branches′ = OrderedDict{Symbol, Trie}()
    for (n, s) in branches(t)
      s′ = filtermap(f, s)
      if !isnothing(s′)
        branches′[n] = s′
      end
      if length(branches′) > 0
        B = valtype(second(first(branches)))
        node(OrderedDict{Symbol, Trie{B}}(branches′))
      end
    end
  end
end

function zipwith(f, t1::Trie, t2::Trie)
  if isleaf(t1) && isleaf(t2)
    leaf(f(t1[], t2[]))
  elseif isnode(t1) && isnode(t2)
    b1, b2 = branches(t1), branches(t2)
    keys(b1) == keys(b2) || error("cannot zip two tries not of the same shape")
    node(OrderedDict(n => zip(s1, s2) for ((n, s1), (_, s2)) in zip(b1, b2)))
  else
    error("cannot zip two tries not of the same shape")
  end
end

Base.zip(t1::Trie, t2::Trie) = zipwith((a,b) -> (a,b), t1, t2)

Base.getindex(p::Trie, n::Symbol) = getproperty(p, n)

function Base.getindex(p::Trie{A})::A where {A}
  if isleaf(p)
    value(p)
  else
    throw(TrieDerefError(p))
  end
end

function Base.first(t::Trie)
  if isleaf(t)
    t[]
  else
    first(first(values(branches(t))))
  end
end

function Base.hasproperty(p::Trie, n::Symbol)
  if isleaf(p)
    false
  else
    haskey(branches(p), n)
  end
end

function Base.propertynames(p::Trie)
  if isleaf(p)
    Symbol[]
  else
    keys(branches(p))
  end
end

Base.keys(p) = Base.propertynames(p)

Base.valtype(p::Trie{A}) where {A} = A
Base.valtype(::Type{Trie{A}}) where {A} = A

function Base.map(f, p::Trie)::Trie
  if isleaf(p)
    leaf(f(p[]))
  else
    d′ = OrderedDict((n => map(f, p′)) for (n, p′) in branches(p))
    B = valtype(valtype(d′))
    Trie{B}(TrieNode{Trie{B}}(d′))
  end
end

function flatten(p::Trie{Trie{A}})::Trie{A} where {A}
  if isleaf(p)
    p[]
  else
    map(flatten, p)
  end
end

struct TrieVar
  content::Union{Nothing, Tuple{Symbol, TrieVar}}
end

PACKAGE_ROOT = TrieVar(nothing)
■ = PACKAGE_ROOT

content(v::TrieVar) = getfield(v, :content)
isroot(v::TrieVar) = isnothing(content(v))
isnested(v::TrieVar) = !isroot(v)

function Base.getproperty(v::TrieVar, n::Symbol)
  if isroot(v)
    TrieVar((n, v))
  else
    (n′, v′) = content(v)
    TrieVar((n′, getproperty(v′, n)))
  end
end

function mapwithkey(f, t::Trie; prefix=PACKAGE_ROOT)
  if isleaf(t)
    leaf(f(prefix, t[]))
  else
    node([k => mapwithkey(f, v; prefix=getproperty(prefix, k)) for (k, v) in branches(t)]...)
  end
end

function fold(base, induction, t::Trie)
  if isleaf(t)
    base(t[])
  else
    induction(OrderedDict(k => fold(base, induction, v) for (k,v) in branches(t)))
  end
end

function Base.all(f, t::Trie)
  fold(f, d -> all(values(d)), t)
end

# precondition: the union of the keys in t1 and t2 is prefix-free
function Base.merge(t1::Trie{A}, t2::Trie{A}) where {A}
  if isleaf(t1) || isleaf(t2)
    error("cannot merge tries with overlapping keys")
  else
    b1, b2 = branches(t1), branches(t2)
    b = OrderedDict{Symbol, Trie{A}}()
    for (n, t) in b1
      if haskey(b2, n)
        b[n] = merge(t, b2[n])
      else
        b[n] = t
      end
    end
    for (n, t) in b2
      if !haskey(b1, n)
        b[n] = t
      end
    end
    node(b)
  end
end

"""
Make a trie out of a dict from trie keys to values.

Fails if the keys in the dict are not prefix-free.
"""
function Trie(d::OrderedDict{TrieVar, A}) where {A}
  branches = OrderedDict{Symbol, OrderedDict{TrieVar, A}}()
  for (v, x) in d
    if isroot(v)
      if length(d) == 1
        return leaf(x)
      else
        error("attempted trie conversion failed because keys were not prefix-free")
      end
    else
      (n, v′) = content(v)
      if haskey(branches, n)
        branches[n][v′] = x
      else
        branches[n] = OrderedDict(v′ => x)
      end
    end
  end
  node(n => Trie(d′) for (n, d′) in branches)
end

Trie(pairs::Pair{TrieVar, A}...) where {A} = Trie(OrderedDict{TrieVar, A}(pairs...))

function Base.show(io::IO, v::TrieVar)
  print(io, "■")
  while !isroot(v)
    (n, v) = content(v)
    print(io, ".", n)
  end
end

function Base.haskey(p::Trie, v::TrieVar)
  if isroot(v)
    isleaf(p)
  else
    (n, v′) = content(v)
    hasproperty(p, n) && haskey(getproperty(p, n), v′)
  end
end

struct TrieVarNotFound <: Exception
  p::Trie
  v::TrieVar
end

function Base.showerror(io::IO, e::TrieVarNotFound)
  println(io, "package variable ", e.v, " does not point to leaf in package")
  println(io, e.p)
end

function Base.getindex(p::Trie, v::TrieVar)
  if isroot(v)
    if isleaf(p)
      p[]
    else
      throw(TrieVarNotFound(p, v))
    end
  else
    (n, v′) = content(v)
    if hasproperty(p, n)
      getproperty(p, n)[v′]
    else
      throw(TrieVarNotFound(p, v))
    end
  end
end

function AbstractTrees.children(p::Trie)
  if isleaf(p)
    ()
  else
    branches(p)
  end
end

function AbstractTrees.printnode(io::IO, p::Trie{A}; kw...) where {A}
  if isleaf(p)
    print(io, p[])
  else
    print(io, "Trie{$A}")
  end
end

function Base.show(io::IO, p::Trie{A}) where {A}
  if isleaf(p)
    print(io, "leaf(", p[], ")::Trie{$A}")
  else
    print_tree(io, p)
  end
end

end
