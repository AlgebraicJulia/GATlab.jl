module ScopeTrees
export ScopeTree, pure, wrap, unwrap, isleaf, isnode,
  ScopeTreeHom

using ....Util
using ....Syntax, ....Models, ...StdTheories
using MLStyle

# Scope Tree
############

struct ScopeTree{T}
  val::Either{T, Scope{ScopeTree{T}, Nothing}}
end

pure(x::T) where {T} = ScopeTree{T}(Left(x))

wrap(s::Scope{ScopeTree{T}, Nothing}) where {T} = ScopeTree{T}(Right(s))

wrap(p::Pair{Symbol, ScopeTree{T}}...) where {T} = wrap(Scope(p...))

unwrap(t::ScopeTree) = t.val.val

isnode(t::ScopeTree) = isright(t.val)

isleaf(t::ScopeTree) = isleft(t.val)

Base.keys(t::ScopeTree) =
  if isleaf(t)
    [Reference()]
  else
    s = unwrap(t)
    vcat([map(r -> Reference(x, r), keys(t′)) for (x,t′) in identvalues(s)]...)
  end

Base.haskey(t::ScopeTree, k::Reference) =
  if isleaf(t) && isempty(k)
    true
  elseif isnode(t) && !isempty(k) && hasident(s, first(k))
    haskey(getvalue(unwrap(t), first(k)), rest(k))
  else
    false
  end

Base.getindex(t::ScopeTree, k::Reference) =
  if isleaf(t) && isempty(k)
    unwrap(t)
  elseif isnode(t) && !isempty(k) && hasident(s, first(k))
    getvalue(unwrap(t), first(k))[rest(k)]
  else
    throw(KeyError(k))
  end

struct ScopeTreeHom{S}
  map::Dict{Reference, Tuple{Reference, S}}
end

struct ScopeTreeC{Ob, Hom, C<:Model{Tuple{Ob, Hom}}} <: Model{Tuple{ScopeTree{Ob}, ScopeTreeHom{Hom}}}
  c::C
end

@instance ThCategory{ScopeTree{Ob}, ScopeTreeHom{Hom}} (;model::ScopeTreeC{Ob, Hom, C}) where {Ob, Hom, C} begin
  Ob(t::ScopeTree{Ob}) =
    if isleaf(t)
      Ob(unwrap(t); model=model.c)
    else
      all(t′ -> Ob(t′; model), getvalues(unwrap(s)))
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
