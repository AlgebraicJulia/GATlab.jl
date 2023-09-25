module TheoryMaps
export IdTheoryMap, TheoryIncl, AbsTheoryMap, TheoryMap, @theorymap,
       TypeMap, TermMap, typemap, termmap

using ..GATs, ..Scopes, ..ExprInterop
using ..Scopes: unsafe_pushbinding!
using ..GATs: InCtx, TrmTyp, bindingexprs, bind_localctx, substitute_term
using ..TheoryInterface
import ..ExprInterop: toexpr, fromexpr

using StructEquality, MLStyle
using DataStructures: OrderedDict

# Theory Maps
#############

"""
TheoryMaps are morphisms in a category of GATs. A TheoryMap X -> Y can be 
thought of in many ways.

1. An "Every model of Y is also a model of X in some way"
2. Providing "X-shaped hooks" into Y.
3. X is a syntax for Y's semantics. 

The main methods for an AbsTheoryMap to implement are: 
  - dom, codom, 
  - typemap: A dictionary of Ident (of AlgTypeConstructor in domain) to
             TypeInCtx (The TypeScope of the TypeInCtx must be structurally 
             identical to the localcontext of the type constructor 
             associated with the key).
  - termmap: A dictionary of Ident (of AlgTermConstructor in domain) to 
             TermInCtx. (The TypeScope of the TrmInCtx must be structurally 
             identical to the localcontext + args of the term constructor 
             associated with the key.)

The requirement that the values of `typemap` and `termmap` be structurally 
identical to the contexts in the domain can eventually be relaxed (to allow 
reordering, additional derived elements, dropping unused arguments), but for now 
we require this for simplicity.
"""
abstract type AbsTheoryMap end

# Category of GATs
#-----------------
dom(f::AbsTheoryMap)::GAT = f.dom # assume this exists by default

codom(f::AbsTheoryMap)::GAT = f.codom # assume this exists by default

function compose(f::AbsTheoryMap, g::AbsTheoryMap)
  typmap = OrderedDict(k => g(v) for (k, v) in pairs(typemap(f)))
  trmmap = OrderedDict(k => g(v) for (k, v) in pairs(termmap(f)))
  TheoryMap(dom(f), codom(g), typmap, trmmap)
end

# Pushing forward terms along a GAT morphism
#-------------------------------------------

(f::AbsTheoryMap)(x::Ident) = pushforward(typemap(f), termmap(f), x) 

(f::AbsTheoryMap)(x...; kw...) = 
  pushforward(dom(f), typemap(f), termmap(f), x...; kw...)

(f::AbsTheoryMap)(c::AlgTerm) =  f(TermInCtx(c))

function (f::AbsTheoryMap)(t::InCtx{T}) where T
  fctx = f(t.ctx)
  InCtx{T}(fctx, f(t.ctx, t.trm; fctx=fctx))
end

"""
Map a (flatten-able) context in the domain theory into a context of the 
codomain theory
"""
function pushforward(
  dom::GAT, 
  tymap::OrderedDict{Ident, TypeInCtx}, 
  trmap::OrderedDict{Ident,TermInCtx}, 
  ctx::TypeCtx
) 
  fctx = TypeScope()
  scope = Scopes.flatten(ctx)
  for i in 1:length(scope)
    b = scope[LID(i)]
    partial_scope = Scope(getbindings(scope)[1:i-1]; tag=gettag(scope))
    val = pushforward(dom, tymap, trmap, partial_scope, getvalue(b); fctx=fctx)
    new_binding = Binding{AlgType, Nothing}(b.primary, val, b.sig)
    unsafe_pushbinding!(fctx, new_binding)
  end
  fctx
end

""" Map a term (or type) `t` in context `c` along `f`. """
function pushforward(
  dom::GAT, 
  tymap::OrderedDict{Ident, TypeInCtx}, 
  trmap::OrderedDict{Ident,TermInCtx},
  ctx::TypeCtx, 
  t::T; 
  fctx=nothing
) where {T<:TrmTyp}
  fctx = isnothing(fctx) ? f(ctx) : fctx
  head = headof(t)
  if hasident(ctx, head)
    retag(Dict(gettag(ctx)=>gettag(fctx)), t) # term is already in the context
  else
    tcon = getvalue(dom[head]) # Toplevel Term (or Type) Constructor of t in domain
    new_term = pushforward(tymap, trmap, head) # Codom TermInCtx associated with the toplevel tcon
    # idents in bind_localctx refer to term constructors args and l.c.
    rt_dict = Dict(gettag(x)=>gettag(new_term.ctx) 
                   for x in [tcon.args, tcon.localcontext])

    # new_term has same context as tcon, so recursively map over components
    lc = bind_localctx(dom, InCtx{T}(ctx, t))
    flc = Dict{Ident, AlgTerm}(map(collect(pairs(lc))) do (k, v)
      if hasident(tcon.args, k) # offset when squashing localcontext and args
        k = Ident(gettag(k), LID(getlid(k).val+length(tcon.localcontext)), nameof(k))
      end
      retag(rt_dict, k) => pushforward(dom, tymap, trmap, ctx, v; fctx)
    end)
    substitute_term(new_term.trm, flc)
  end
end

function pushforward(tymap, trmap, s::Ident) 
  if haskey(tymap, s)
    tymap[s] 
  elseif haskey(trmap, s)
    trmap[s]
  else 
    throw(KeyError("Cannot find key $s"))
  end
end

# ID 
#---
@struct_hash_equal struct IdTheoryMap <: AbsTheoryMap
  gat::GAT
end

dom(f::IdTheoryMap)::GAT = f.gat

codom(f::IdTheoryMap)::GAT = f.gat

compose(f::IdTheoryMap, ::IdTheoryMap) = f

compose(::IdTheoryMap, g::AbsTheoryMap) = g

compose(f::AbsTheoryMap, ::IdTheoryMap) = f

"""Invert a theory iso"""
Base.inv(f::IdTheoryMap) = f


# Inclusion 
#----------

"""
A theory inclusion has a subset of scopes 
"""
@struct_hash_equal struct TheoryIncl <: AbsTheoryMap
  dom::GAT
  codom::GAT
  function TheoryIncl(dom,codom) 
    err = "Cannot construct TheoryInclusion"
    dom ⊆ codom ? new(dom,codom) : error(err)
  end
end

typemap(ι::Union{IdTheoryMap,TheoryIncl}) = 
  OrderedDict(k => TypeInCtx(dom(ι), k) for k in typecons(dom(ι)))

termmap(ι::Union{IdTheoryMap,TheoryIncl}) = 
  OrderedDict(k=>TermInCtx(dom(ι), k) for k in termcons(dom(ι)))

compose(f::TheoryIncl, g::TheoryIncl) = TheoryIncl(dom(f), codom(g))

compose(f::AbsTheoryMap, g::TheoryIncl) = 
  TheoryIncl(dom(f), codom(g), typemap(f), termmap(f))

Base.inv(f::TheoryIncl) = 
  dom(f) == codom(f) ? f : error("Cannot invert a nontrivial theory inclusion")

# General theory map 
#-------------------

"""
Presently, axioms are not mapped to proofs.

TODO: check that it is well-formed, axioms are preserved.
"""
@struct_hash_equal struct TheoryMap <: AbsTheoryMap
  dom::GAT
  codom::GAT
  typemap::OrderedDict{Ident,TypeInCtx}
  termmap::OrderedDict{Ident,TermInCtx}
  function TheoryMap(dom, codom, typmap, trmmap)
    missing_types = setdiff(Set(keys(typmap)), Set(typecons(dom))) 
    missing_terms = setdiff(Set(keys(trmmap)), Set(termcons(dom))) 
    isempty(missing_types) || error("Missing types $missing_types")
    isempty(missing_terms) || error("Missing types $missing_terms")

    tymap′, trmap′ = map([typmap, trmmap]) do tmap 
      OrderedDict(k => v isa Ident ? InCtx(codom, v) : v for (k,v) in pairs(tmap))
    end

    new(dom, codom, tymap′, trmap′)
  end
end

typemap(t::TheoryMap) = t.typemap

termmap(t::TheoryMap) = t.termmap

"""Invert a theory iso"""
# Base.inv(::TheoryMap) = error("Not implemented")


# Serialization
#--------------
function toexpr(m::AbsTheoryMap)
  typs, trms = map([typemap(m),termmap(m)]) do tm 
    map(collect(tm)) do (k,v)
      domterm = toexpr(dom(m), InCtx(dom(m), k))
      Expr(:call, :(=>), domterm, toexpr(AppendScope(codom(m), v.ctx), v.trm)) 
    end
  end
  Expr(:block, typs...,trms...)
end

#TODO: we currently ignore LineNumberNodes. TheoryMap data structure could 
#      instead use scopes (rather than OrderedDicts) which store this info in 
#      Bindings.
function fromexpr(dom::GAT, codom::GAT, e, ::Type{TheoryMap})
  tyms = OrderedDict{Ident, TypeInCtx}()
  trms = OrderedDict{Ident, TermInCtx}()
  exprs = @match e begin
    Expr(:block, e1::Expr, es...) => [e1,es...]
    Expr(:block, ::LineNumberNode, es...) => filter(x->!(x isa LineNumberNode), es)
  end
  for expr in exprs
    e1, e2 = @match expr begin Expr(:call, :(=>), e1, e2) => (e1,e2) end
    key = fromexpr(dom, e1, InCtx; constants=false)
    T = only(typeof(key).parameters)
    keyhead = key.trm.head
    
    # reorder the context to match that of the canonical localctx + args
    tc = getvalue(dom[keyhead])
    reorder_init = Dict(zip(length(tc.localcontext).+ collect(1:length(tc.args)), 
                        getvalue.(getlid.(headof.(key.trm.args)))))
    reordered_ctx = reorder(key.ctx, Scopes.flatten(argcontext(tc)), reorder_init)

    fctx = pushforward(dom, tyms, trms, reordered_ctx)
    val = fromexpr(AppendScope(codom, fctx), e2, T)
    dic = T == AlgType ? tyms : trms
    dic[key.trm.head] = InCtx{T}(fctx, val)
  end
  TheoryMap(dom, codom, tyms, trms)
end

"""
The result of:

reorder([(B,C,A)::Ob, G::B→C, F::A→B], [(a,b,c)::Ob, f::a→b, g::b→c], {4->5, 5->4})

Is the reordered first context: [(A,B,C)::Ob, F::A→B, G::B→C]
"""
function reorder(domctx::Scope{T,Sig}, codomctx::Scope{T, Sig}, perm::Dict{Int,Int}) where {T,Sig}
  N = length(domctx)
  N == length(codomctx) || error("Mismatched lengths $N != $(length(codomctx))")
  for dom_i in reverse(1:N)
    codom_i = perm[dom_i] 
    dom_lids, codom_lids = map([domctx=>dom_i, codomctx=>codom_i]) do (ctx, i) 
      getvalue.(getlid.(headof.(argsof(getvalue(ctx[LID(i)])))))
    end
    for (dom_j, codom_j) in zip(dom_lids, codom_lids)
      if !haskey(perm, dom_j)
        perm[dom_j] = codom_j
      elseif perm[dom_j] != codom_j
        error("inconsistent")
      end
    end
  end
  isperm(collect(values(perm))) || error("We need to permute the LIDs")
  Scope([reorder(domctx[LID(perm[i])], gettag(domctx), perm) for i in 1:N], 
        aliases=domctx.aliases, tag=gettag(domctx))
end

"""Change LIDs recursively"""
function reorder(t::T, tag::ScopeTag, perm::Dict{Int,Int}) where T <: TrmTyp
  args = AlgTerm[reorder.(argsof(t), Ref(tag), Ref(perm))...]
  head = headof(t) 
  if head isa Ident && gettag(head) == tag
    T(Ident(gettag(head), LID(perm[getvalue(getlid(head))]), nameof(head)), args)
  else 
    T(head, args)
  end
end

reorder(b::Binding{T, Sig}, tag::ScopeTag, perm::Dict{Int,Int}) where {T,Sig} = 
  setvalue(b, reorder(getvalue(b), tag, perm))


macro theorymap(head, body)
  (name, domname, codomname) = @match head begin
    Expr(:call, name, domname, codomname) => (name, domname, codomname)
    _ => error("could not parse head of @theory: $head")
  end

  dommod = macroexpand(__module__, :($domname.@theory_module))
  codommod = macroexpand(__module__, :($codomname.@theory_module))
  dom = macroexpand(__module__, :($domname.@theory))
  codom = macroexpand(__module__, :($codomname.@theory))
  tmap = fromexpr(dom, codom, body, TheoryMap)

  esc(
    Expr(
      :toplevel,
      :(
        module $name
          const MAP = $tmap
          macro map() $tmap end
          macro dom() $dommod end
          macro codom() $codommod end
        end
      ),
      :(Core.@__doc__ $(name)),
    )
  )
end

end # module
