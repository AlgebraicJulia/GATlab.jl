module TheoryMaps
export IdTheoryMap, TheoryIncl, AbsTheoryMap, TheoryMap, @theorymap,
       TypeMap, TermMap, typemap, termmap

using ..GATs, ..Scopes, ..ExprInterop
using ..Scopes: unsafe_pushbinding!
using ..GATs: InCtx, bindingexprs, substitute_term
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
  InCtx{T}(fctx, f(t.ctx, t.val; fctx=fctx))
end

"""
Map a (flatten-able) context in the domain theory into a context of the 
codomain theory
"""
function pushforward(
  dom::GAT, 
  tymap::OrderedDict{Ident, TypeInCtx}, 
  trmap::OrderedDict{Ident,TermInCtx}, 
  scope::TypeCtx
) 
  fctx = TypeScope()
  for i in 1:length(scope)
    b = scope[LID(i)]
    partial_scope = Scope(getbindings(scope)[1:i-1]; tag=gettag(scope))
    val = pushforward(dom, tymap, trmap, partial_scope, getvalue(b); fctx=fctx)
    new_binding = Binding{AlgType}(nameof(b), val)
    unsafe_pushbinding!(fctx, new_binding)
  end
  fctx
end

""" Map a term (or type) `t` in context `c` along `f`. """
function pushforward(
  dom::GAT, 
  tymap::OrderedDict{Ident, TypeInCtx}, 
  trmap::OrderedDict{Ident, TermInCtx},
  ctx::TypeCtx, 
  t::T; 
  fctx=nothing
) where T<:AlgAST
  fctx = isnothing(fctx) ? f(ctx) : fctx
  b = bodyof(t)
  if GATs.isvariable(t)
    hasident(ctx, b) || error("Unknown variable $t")
    retag(Dict(gettag(ctx)=>gettag(fctx)), t) # term is already in the context
  else
    head = methodof(b)
    tcon = getvalue(dom[head]) # Toplevel Term (or Type) Constructor of t in domain
    new_term = pushforward(tymap, trmap, head) # Codom TermInCtx associated with the toplevel tcon
    # idents in bind_localctx refer to term constructors args and l.c.
    rt_dict = Dict(gettag(tcon.localcontext)=>gettag(new_term.ctx))

    # new_term has same context as tcon, so recursively map over components
    lc = bind_localctx(GATContext(dom), InCtx{T}(ctx, t))
    flc = Dict{Ident, AlgTerm}(map(collect(pairs(lc))) do (k, v)
      retag(rt_dict, k) => pushforward(dom, tymap, trmap, ctx, v; fctx)
    end)
    substitute_term(new_term.val, flc)
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


"""
Infer the type of the term of a term. If it is not in context, recurse on its 
arguments. The term constructor's output type yields the resulting type once
its localcontext variables are substituted with the relevant AlgTerms. 

              (x,y,z)::Ob, p::Hom(x,y), q::Hom(y,z)
E.g. given    --------------------------------------
                           id(x)⋅(p⋅q)

                 (a,b,c)::Ob, f::Hom(a,b), g::Hom(b,c)
and output type:  ------------------------------------
                              Hom(a,c)
                              
We first recursively find `{id(x) => Hom(x,x), p⋅q => Hom(x,z)}`. We ultimately 
want an AlgTerm for everything in the output type's context such that we can 
substitute into `Hom(a,c)` to get the final answer. It will help to also compute 
the AlgType for everything in the context. We work backwards, since we start by
knowing `{f => id(x)::Hom(x,x), g=> p⋅q :: Hom(x,z)}`. For `a` `b` and `c`, 
we use `equations` which tell us, e.g., that `a = dom(f)`. So we can grab the 
first argument of the *type* of `f` (i.e. grab `x` from `Hom(x,x)`). 
"""
function infer_type(ctx::Context, t::AlgTerm)
  b = bodyof(t)
  if GATs.isvariable(t)
    getvalue(ctx[b])
  else 
    head = methodof(b)
    tc = getvalue(ctx[head])
    typed_terms = bind_localctx(ctx, t)
    typ = bodyof(tc.type)
    args = substitute_term.(argsof(typ), Ref(typed_terms))
    AlgType(headof(typ), methodof(typ), args)
  end
end

infer_type(ctx::Context, t::TermInCtx) = infer_type(AppendScope(ctx, t.ctx), t.val)

"""
Take a term constructor and determine terms of its local context.

This function is mutually recursive with `infer_type`. 
""" 
bind_localctx(ctx::GATContext, t::InCtx) = 
  bind_localctx(GATContext(ctx.theory, AppendContext(ctx.context, t.ctx)), t.val)

function bind_localctx(ctx::GATContext, t::AlgAST)
  m = methodof(t.body)
  tc = getvalue(ctx[m])
  eqs = equations(ctx.theory, m)
  typed_terms = Dict{Ident, Pair{AlgTerm,AlgType}}()
  for (i,a) in zip(tc.args, t.body.args)
    tt = (a => infer_type(ctx, a))
    typed_terms[ident(tc, lid=i, level=1)] = tt 
  end

  for lc_arg in reverse(getidents(getcontext(tc)))
    if getlid(lc_arg) ∈ tc.args 
      continue 
    end 
    # one way of determining lc_arg's value
    app = bodyof(first(filter(GATs.isapp, eqs[lc_arg])))
    to = bodyof(only(argsof(app)))
    m = methodof(app)
    inferred_term = typed_terms[to][2].body.args[getvalue(ctx.theory[m]).arg]
    inferred_type = infer_type(ctx, inferred_term)
    typed_terms[lc_arg] = inferred_term => inferred_type
  end

  Dict([k=>v[1] for (k,v) in pairs(typed_terms)])
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
  OrderedDict(k => TypeInCtx(dom(ι), k) for k in last.(typecons(dom(ι))))

termmap(ι::Union{IdTheoryMap,TheoryIncl}) = 
  OrderedDict(k=>TermInCtx(dom(ι), k) for k in last.(termcons(dom(ι))))

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
    missing_types = setdiff(Set(keys(typmap)), Set(last.(typecons(dom)))) 
    missing_terms = setdiff(Set(keys(trmmap)), Set(last.(termcons(dom)))) 
    isempty(missing_types) || error("Missing types $missing_types")
    isempty(missing_terms) || error("Missing terms $missing_terms")

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
  typs, trms = map([typemap(m), termmap(m)]) do tm 
    map(collect(tm)) do (k,v)
      domterm = toexpr(dom(m), InCtx(dom(m), k))
      Expr(:call, :(=>), domterm, toexpr(AppendContext(codom(m), v.ctx), v.val)) 
    end
  end
  Expr(:block, typs...,trms...)
end

#TODO: we currently ignore LineNumberNodes. TheoryMap data structure could 
#      instead use scopes (rather than OrderedDicts) which store this info in 
#      Bindings.
function fromexpr(dom::GAT, codom::GAT, e, ::Type{TheoryMap})
  typs = OrderedDict{Ident, TypeInCtx}()
  trms = OrderedDict{Ident, TermInCtx}()
  exprs = @match e begin
    Expr(:block, e1::Expr, es...) => [e1,es...]
    Expr(:block, ::LineNumberNode, es...) => filter(x->!(x isa LineNumberNode), es)
  end
  for expr in exprs
    e1, e2 = @match expr begin Expr(:call, :(=>), e1, e2) => (e1,e2) end
    flat_term, ctx = @match e1 begin 
      Expr(:call, :⊣, flat_term, tscope) => begin 
        flat_term, fromexpr(dom, tscope, TypeScope)
      end
      _ => (e1, TypeScope())
    end
    xname, argnames = @match flat_term begin 
      s::Symbol => (s, []) 
      Expr(:call, f::Symbol, args...) => (f, args)
    end

    is_term = xname ∈ nameof.(first.(termcons(dom)))
    T = is_term ? AlgTerm : AlgType

    args = idents(ctx; name=argnames)
    sig = [AlgSort(getvalue(ctx[i])) for i in args]
    x = ident(dom; name=xname)
    m = GATs.methodlookup(GATContext(dom), x, sig)

    # reorder the context to match that of the canonical localctx + args
    tc = getvalue(dom[m])
    reorder_init = Dict(zip(getvalue.(getlid.(args)), getvalue.(tc.args)))
    reordered_ctx = reorder(ctx, tc.localcontext, reorder_init)
    fctx = pushforward(dom, typs, trms, reordered_ctx)
    val = fromexpr(GATContext(codom, fctx), e2, T)
    dic = T == AlgType ? typs : trms
    dic[m] = InCtx{T}(fctx, val)
  end
  TheoryMap(dom, codom, typs, trms)
end

"""
The result of:

reorder([(B,C,A)::Ob, G::B→C, F::A→B], [(a,b,c)::Ob, f::a→b, g::b→c], {4->5, 5->4})

Is the reordered first context: [(A,B,C)::Ob, F::A→B, G::B→C]
"""
function reorder(domctx::TypeScope, codomctx::TypeScope, perm::Dict{Int,Int})
  N = length(domctx)
  N == length(codomctx) || error("Mismatched lengths $N != $(length(codomctx))")
  for dom_i in reverse(1:N)
    codom_i = perm[dom_i] 
    dom_lids, codom_lids = map([domctx=>dom_i, codomctx=>codom_i]) do (ctx, i) 
      map(bodyof.(argsof(getvalue(ctx[LID(i)]).body))) do arg 
        getvalue(getlid(arg))
      end
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

  TypeScope(Binding{AlgType}[reorder(domctx[LID(perm[i])], gettag(domctx), perm) for i in 1:N], 
             tag=gettag(domctx))
end

"""Change LIDs recursively"""
function reorder(t::T, tag::ScopeTag, perm::Dict{Int,Int}) where T<:AlgAST
  b = bodyof(t)
  if GATs.isvariable(t)
    if gettag(b) == tag 
      AlgTerm(Ident(gettag(b), LID(perm[getvalue(getlid(b))]), nameof(b)))
    else 
      t 
    end
  else 
    args = AlgTerm[reorder.(argsof(b), Ref(tag), Ref(perm))...]
    T(headof(b), methodof(b), args)
  end
end


reorder(b::Binding{T}, tag::ScopeTag, perm::Dict{Int,Int}) where {T} = 
  setvalue(b, reorder(getvalue(b), tag, perm))


macro theorymap(head, body)
  (name, domname, codomname) = @match head begin
    Expr(:call, name, domname, codomname) => (name, domname, codomname)
    _ => error("could not parse head of @theory: $head")
  end

  dommod = macroexpand(__module__, :($domname.Meta.@theory_module))
  codommod = macroexpand(__module__, :($codomname.Meta.@theory_module))
  dom = macroexpand(__module__, :($domname.Meta.@theory))
  codom = macroexpand(__module__, :($codomname.Meta.@theory))
  tmap = fromexpr(dom, codom, body, TheoryMap)

  mig = migrator(tmap, dommod, codommod, dom, codom)

  esc(
    Expr(
      :toplevel,
      :(
        module $name
          const MAP = $tmap
          macro map() $tmap end
          macro dom() $dommod end
          macro codom() $codommod end

          $mig
        end
      ),
      :(Core.@__doc__ $(name)),
    )
  )
end

function migrator end


end # module
