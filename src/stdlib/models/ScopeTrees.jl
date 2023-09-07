module ScopeTrees
export ScopeTree, ScopeLeaf, ScopeNode, pure, wrap, unwrap, isleaf, isnode,
  ScopeTreeHom, ScopeTreeC

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

function ScopeTreeHom(pairs::Pair{Reference, Tuple{Reference, S}}...) where {S}
  ScopeTreeHom{S}(Dict{Reference, Tuple{Reference, S}}(pairs...))
end

struct ScopeTreeC{ObT, HomT, C<:Model{Tuple{ObT, HomT}}} <: Model{Tuple{ScopeTree{ObT}, ScopeTreeHom{HomT}}}
  c::C
end

using .ThCategory

function seteq(x, y)
  (x ⊆ y) && (y ⊆ x)
end

@instance ThCategory{ScopeTree{ObT}, ScopeTreeHom{HomT}} (;model::ScopeTreeC{ObT, HomT, C}) where {ObT, HomT, C} begin
  Ob(t::ScopeTree{ObT}) = @match t begin
    ScopeLeaf(x) => Ob(x; model=model.c)
    ScopeNode(s) => all(t′ -> Ob(t′; model), values(s))
  end

  function Hom(f::ScopeTreeHom{HomT}, x::ScopeTree{ObT}, y::ScopeTree{ObT})
    seteq(keys(f.map), keys(x)) && seteq(first.(values(f.map)), keys(y)) || return false
    all(Hom(f₀, x[i], y[j]; model=model.c) for (i, (j, f₀)) in f.map)
  end

  id(x::ScopeTree{ObT}) = ScopeTreeHom{HomT}(k => (k, id(x[k]; model=model.c)))

  function compose(f::ScopeTreeHom{HomT}, g::ScopeTreeHom{HomT}; context)
    if !isnothing(context)
      [:a,:b,:c] ⊂ keys(context) || error("must provide full context or nothing")
    end

    ScopeTreeHom{HomT}(
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
