module ScopeTrees
export ScopeTree, ScopeLeaf, ScopeNode, pure, wrap, unwrap, isleaf, isnode,
  ScopeTreeHom

using ....Syntax, ....Models, ...StdTheories
using MLStyle

# Scope Tree
############

@data ScopeTree{T} <: HasContext begin
  ScopeLeaf(T)
  ScopeNode(Scope{ScopeTree{T}, Nothing})
end

Scopes.getcontext(t::ScopeTree) = @match t begin
  ScopeLeaf(_) => EmptyContext()
  ScopeNode(s) => s
end

pure(x::T) where {T} = ScopeLeaf{T}(x)

wrap(s::Scope{ScopeTree{T}}) where {T} = ScopeNode{T}(s)

wrap(p::Pair{Symbol,<:ScopeTree{T}}...) where {T} = wrap(Scope{ScopeTree{T}}(p...))

unwrap(t::ScopeTree) = @match t begin
  ScopeLeaf(x) => x
  ScopeNode(s) => s
end

isleaf(t::ScopeTree) = @match t begin
  ScopeLeaf(_) => true
  ScopeNode(_) => false
end

isnode(t::ScopeTree) = @match t begin
  ScopeLeaf(_) => false
  ScopeNode(_) => true
end

Base.keys(t::ScopeTree) = @match t begin
  ScopeLeaf(_) => [Reference()]
  ScopeNode(s) => vcat([map(r -> Reference(x, r), keys(t)) for (x,t) in identvalues(s)]...)
end

Base.haskey(t::ScopeTree, k::Reference) = @match t begin
  ScopeLeaf(_) && if isempty(k) end => true
  ScopeNode(s) && if !isempty(k) && hasident(s, first(k)) end => haskey(getvalue(s, first(k)), rest(k))
  _ => false
end

Base.getindex(t::ScopeTree, k::Reference) = @match t begin
  ScopeLeaf(x) && if isempty(k) end => x
  ScopeNode(s) && if !isempty(k) && hasident(s, first(k)) end => getvalue(s, first(k))[rest(k)]
  _ => throw(KeyError(k))
end

struct ScopeTreeHom{S}
  map::Dict{Reference, Tuple{Reference, S}}
end

struct ScopeTreeC{Ob, Hom, C<:Model{Tuple{Ob, Hom}}} <: Model{Tuple{ScopeTree{Ob}, ScopeTreeHom{Hom}}}
  c::C
end

@instance ThCategory{ScopeTree{Ob}, ScopeTreeHom{Hom}} (;model::ScopeTreeC{Ob, Hom, C}) where {Ob, Hom, C} begin
  Ob(t::ScopeTree{Ob}) = @match t begin
    ScopeLeaf(x) => Ob(x; model=model.c)
    ScopeNode(s) => all(t′ -> Ob(t′; model), getvalues(s))
  end

  function Hom(f::ScopeTreeHom{Hom}, x::ScopeTree{Ob}, y::ScopeTree{Ob})
    Set(keys(f.map)) == keys(x) && Set(first.(values(f.map))) == keys(y) || return false
    all(Hom(f₀, x[i], y[j]; model=model.c) for (i, (j, f)) in f.map)
  end

  id(x::ScopeTree{Ob}) = ScopeTreeHom{Hom}(k => (k, id(x[k]; model=model.c)))

  function compose(f::ScopeTreeHom{Hom}, g::ScopeTreeHom{Hom}; context)
    if !isnothing(context)
      [:a,:b,:c] ⊂ keys(context) || error("must provide full context or nothing")
    end

    ScopeTreeHom{Hom}(
      k => begin
        (k′, f₀) = f.map[k]
        (k″, g₀) = g.map[k′]
        localcontext = if !isnothing(context)
          (a=context.a[k], b=context.b[k′], c=context.c[k″])
        else
          nothing
        end
        (k″, compose(f₀, g₀; localcontext))
      end
      for k in keys(f.map)
    )
  end
end

end
