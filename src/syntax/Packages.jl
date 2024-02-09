module Packages

using AbstractTrees

export Package, namespace, singleton, PACKAGE_ROOT, ■, PackageVar

struct Namespace{X}
  values::Dict{Symbol, X}
end

struct Singleton{A}
  value::A
end

struct Package{A}
  content::Union{Singleton{A}, Namespace{Package{A}}}
end

content(p::Package) = getfield(p, :content)
issingleton(p::Package) = content(p) isa Singleton
singleton(x::A) where {A} = Package{A}(Singleton{A}(x))
isnamespace(p::Package) = content(p) isa Namespace
namespace(d::Dict{Symbol, Package{A}}) where {A} = Package{A}(Namespace{Package{A}}(d))
namespace(ps::Pair{Symbol, Package{A}}...) where {A} = namespace(Dict{Symbol, Package{A}}(ps...))

struct PackageIndexError <: Exception
  package::Package
  key::Symbol
end


struct PackageDerefError <: Exception
  package::Package
end

function Base.getproperty(p::Package{A}, n::Symbol)::Package{A} where {A}
  if isnamespace(p)
    d = content(p).values
    if haskey(d, n)
      d[n]
    else
      throw(PackageIndexError(p, n))
    end
  else
    throw(PackageIndexError(p, n))
  end
end

Base.getindex(p::Package, n::Symbol) = getproperty(p, n)

function Base.getindex(p::Package{A})::A where {A}
  if issingleton(p)
    content(p).value
  else
    throw(PackageDerefError(p))
  end
end

function Base.hasproperty(p::Package, n::Symbol)
  if issingleton(p)
    false
  else
    haskey(content(p).values, n)
  end
end

function Base.propertynames(p::Package)
  if issingleton(p)
    Symbol[]
  else
    keys(content(p).values)
  end
end

Base.keys(p) = Base.propertynames(p)

Base.valtype(p::Package{A}) where {A} = A

function Base.map(f, p::Package)::Package
  if issingleton(p)
    singleton(f(p[]))
  else
    d′ = Dict(map(pairs(content(p).values)) do (n, p′)
      (n, map(f, p′))
    end)
    B = valtype(valtype(d′))
    Package{B}(Namespace{Package{B}}(d′))
  end
end

function flatten(p::Package{Package{A}})::Package{A} where {A}
  if issingleton(p)
    content(p).value
  else
    map(flatten, p)
  end
end

struct PackageVar
  content::Union{Nothing, Tuple{Symbol, PackageVar}}
end

PACKAGE_ROOT = PackageVar(nothing)
■ = PACKAGE_ROOT

content(v::PackageVar) = getfield(v, :content)
isroot(v::PackageVar) = isnothing(content(v))
isnested(v::PackageVar) = !isroot(v)

function Base.getproperty(v::PackageVar, n::Symbol)
  if isroot(v)
    PackageVar((n, v))
  else
    (n′, v′) = content(v)
    PackageVar((n′, getproperty(v′, n)))
  end
end

function Base.show(io::IO, v::PackageVar)
  print(io, "■")
  while !isroot(v)
    (n, v) = content(v)
    print(io, ".", n)
  end
end

function Base.haskey(p::Package, v::PackageVar)
  if isroot(v)
    issingleton(p)
  else
    (n, v′) = content(v)
    hasproperty(p, n) && haskey(getproperty(p, n), v′)
  end
end

struct PackageVarNotFound <: Exception
  p::Package
  v::PackageVar
end

function Base.showerror(io::IO, e::PackageVarNotFound)
  println(io, "package variable ", e.v, " does not point to leaf in package")
  println(io, e.p)
end

function Base.getindex(p::Package, v::PackageVar)
  if isroot(v)
    if issingleton(p)
      p[]
    else
      throw(PackageVarNotFound(p, v))
    end
  else
    (n, v′) = content(v)
    if hasproperty(p, n)
      getproperty(p, n)[v′]
    else
      throw(PackageVarNotFound(p, v))
    end
  end
end

function AbstractTrees.children(p::Package)
  if issingleton(p)
    ()
  else
    pairs(content(p).values)
  end
end

function AbstractTrees.printnode(io::IO, p::Package{A}; kw...) where {A}
  if issingleton(p)
    print(io, p[])
  else
    print(io, "Package{$A}")
  end
end

function Base.show(io::IO, p::Package{A}) where {A}
  if issingleton(p)
    print(io, "singleton(", p[], ")::Package{$A}")
  else
    print_tree(io, p)
  end
end

end
