module Tries

using AbstractTrees

export Trie, PACKAGE_ROOT, ■, TrieVar

struct TrieNode{X}
  values::OrderedDict{Symbol, X}
end

struct TrieLeaf{A}
  value::A
end

struct Trie{A}
  content::Union{TrieLeaf{A}, TrieNode{Trie{A}}}
end

content(p::Trie) = getfield(p, :content)
isleaf(p::Trie) = content(p) isa TrieLeaf
leaf(x::A) where {A} = Trie{A}(TrieLeaf{A}(x))
isnode(p::Trie) = content(p) isa TrieNode
node(d::OrderedDict{Symbol, Trie{A}}) where {A} = Trie{A}(TrieNode{Trie{A}}(d))
node(ps::Pair{Symbol, Trie{A}}...) where {A} = node(OrderedDict{Symbol, Trie{A}}(ps...))

struct TrieIndexError <: Exception
  package::Trie
  key::Symbol
end


struct TrieDerefError <: Exception
  package::Trie
end

function Base.getproperty(p::Trie{A}, n::Symbol)::Trie{A} where {A}
  if isnode(p)
    d = content(p).values
    if haskey(d, n)
      d[n]
    else
      throw(TrieIndexError(p, n))
    end
  else
    throw(TrieIndexError(p, n))
  end
end

Base.getindex(p::Trie, n::Symbol) = getproperty(p, n)

function Base.getindex(p::Trie{A})::A where {A}
  if isleaf(p)
    content(p).value
  else
    throw(TrieDerefError(p))
  end
end

function Base.hasproperty(p::Trie, n::Symbol)
  if isleaf(p)
    false
  else
    haskey(content(p).values, n)
  end
end

function Base.propertynames(p::Trie)
  if isleaf(p)
    Symbol[]
  else
    keys(content(p).values)
  end
end

Base.keys(p) = Base.propertynames(p)

Base.valtype(p::Trie{A}) where {A} = A

function Base.map(f, p::Trie)::Trie
  if isleaf(p)
    leaf(f(p[]))
  else
    d′ = OrderedDict(map(pairs(content(p).values)) do (n, p′)
      (n, map(f, p′))
    end)
    B = valtype(valtype(d′))
    Trie{B}(TrieNode{Trie{B}}(d′))
  end
end

function flatten(p::Trie{Trie{A}})::Trie{A} where {A}
  if isleaf(p)
    content(p).value
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
    pairs(content(p).values)
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
