module TheoryMaps
export IdTheoryMap, TheoryIncl, AbsTheoryMap, TheoryMap, @theorymap,
       TypeMap, TermMap, typemap, termmap

using ..GATs, ..Scopes, ..ExprInterop
using ..Scopes: unsafe_pushbinding!
using ..GATs: InCtx, TrmTyp, bindingexprs, bind_localctx, substitute_term

import ..ExprInterop: toexpr, fromexpr

using StructEquality, MLStyle

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
  typmap = Dict(k => g(v) for (k, v) in pairs(typemap(f)))
  trmmap = Dict(k => g(v) for (k, v) in pairs(termmap(f)))
  TheoryMap(dom(f), codom(g), typmap, trmmap)
end

function (t::AbsTheoryMap)(s::Ident) 
  if haskey(typemap(t), s)
    typemap(t)[s] 
  elseif haskey(termmap(t), s)
    termmap(t)[s]
  else 
    throw(KeyError("Cannot find key $s"))
  end
end


(f::AbsTheoryMap)(c::AlgTerm) =  f(TermInCtx(c))

"""Map a context in the domain theory into a context of the codomain theory"""
function (f::AbsTheoryMap)(ctx::TypeScope) 
  fctx = TypeScope()
  for i in 1:length(ctx)
    b = ctx[LID(i)]
    partial_scope = Scope(getbindings(ctx)[1:i-1]; tag=gettag(ctx))
    val = f(partial_scope, getvalue(b), fctx)
    new_binding = Binding{AlgType, Nothing}(b.primary, b.aliases, val, b.sig)
    unsafe_pushbinding!(fctx, new_binding)
  end
  fctx
end

function (f::AbsTheoryMap)(t::InCtx{T}) where T
  fctx = f(t.ctx)
  InCtx{T}(fctx, f(t.ctx, t.trm, fctx))
end

""" Map a term (or type) `t` in context `c` along `f`. """
function (f::AbsTheoryMap)(ctx::TypeScope, t::T, fctx=nothing) where {T<:TrmTyp}
  fctx = isnothing(fctx) ? f(ctx) : fctx
  head = headof(t)
  if hasident(ctx, head)
    retag(Dict(gettag(ctx)=>gettag(fctx)), t) # term is already in the context
  else 
    termcon = getvalue(f.dom[head]) # Toplevel TermConstructor of t in domain
    new_term = f(head) # Codom TermInCtx associated with the toplevel termcon

    # idents in bind_localctx refer to term constructors args and l.c.
    rt_dict = Dict(gettag(x)=>gettag(new_term.ctx) 
                   for x in [termcon.args, termcon.localcontext])

    # new_term has same context as termcon, so recursively map over components
    lc = bind_localctx(f.dom, InCtx{T}(ctx, t))
    flc = Dict{Ident, AlgTerm}(map(collect(pairs(lc))) do (k, v)
      if hasident(termcon.args, k) # offset when squashing localcontext and args
        k = Ident(gettag(k), LID(getlid(k).val+length(termcon.localcontext)), nameof(k))
      end
      retag(rt_dict, k) => f(ctx, v, fctx)
    end)
    substitute_term(new_term.trm, flc)
  end
end

function toexpr(m::AbsTheoryMap)
  typs = map(collect(typemap(m))) do (k, v)
    Expr(:call, :(=>), toexpr(dom(m), k), toexpr(codom(m), v))
  end
  trms = map(collect(termmap(m))) do (k,v)
    domterm = toexpr(dom(m), InCtx(dom(m), k))
    Expr(:call, :(=>), domterm, toexpr(codom(m), v)) 
  end
  Expr(:block, typs...,trms...)
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
  Dict(k => TypeInCtx(dom(ι), k) for k in typecons(dom(ι)))

termmap(ι::Union{IdTheoryMap,TheoryIncl}) = 
  Dict(k=>TermInCtx(dom(ι), k) for k in termcons(dom(ι)))

compose(f::TheoryIncl, g::TheoryIncl) = TheoryIncl(dom(f), codom(g))

compose(f::AbsTheoryMap, g::TheoryIncl) = 
  TheoryIncl(dom(f), codom(g), typemap(f), termmap(f))

Base.inv(f::TheoryIncl) = 
  dom(f) == codom(f) ? f : error("Cannot invert a nontrivial theory inclusion")

# Non-inclusion 
#--------------

"""
Presently, axioms are not mapped to proofs.

TODO: check that it is well-formed, axioms are preserved.
"""
@struct_hash_equal struct TheoryMap <: AbsTheoryMap
  dom::GAT
  codom::GAT
  typemap::Dict{Ident,TypeInCtx}
  termmap::Dict{Ident,TermInCtx}
  function TheoryMap(dom, codom, typmap, trmmap)
    missing_types = setdiff(Set(keys(typmap)), Set(typecons(dom))) 
    missing_terms = setdiff(Set(keys(trmmap)), Set(termcons(dom))) 
    isempty(missing_types) || error("Missing types $missing_types")
    isempty(missing_terms) || error("Missing types $missing_terms")

    tymap′, trmap′ = map([typmap, trmmap]) do tmap 
      Dict(k => v isa Ident ? InCtx(codom, v) : v for (k,v) in pairs(tmap))
    end

    f = new(dom, codom, tymap′, trmap′)
    # Check type/term constructors are coherent
    for (typtrm, tmap) in ["type"=>tymap′, "term"=>trmap′]
      for (k, v) in pairs(tmap)
        f_args = f(argcontext(getvalue(dom[k])))
        arg_fs = v.ctx
        err = "Bad $typtrm map $k => $v ($f_args != $arg_fs)"
        Scopes.equiv(f_args, arg_fs) || error(err)
      end
    end

    f
  end
end

typemap(t::TheoryMap) = t.typemap

termmap(t::TheoryMap) = t.termmap

"""
TODO: we currently ignore LineNumberNodes. TheoryMap data structure could 
      instead use scopes (rather than Dicts) which store this info in Bindings.

TODO: handle more ambiguity via type inference
"""
function fromexpr(dom::GAT, codom::GAT, e, ::Type{TheoryMap})
  tyms = Dict{Ident, Union{Ident, TypeInCtx}}()
  trms = Dict{Ident, Union{Ident, TermInCtx}}()
  exprs = @match e begin
    Expr(:block, e1::Expr, es...) => [e1,es...]
    Expr(:block, ::LineNumberNode, es...) => filter(x->!(x isa LineNumberNode), es)
  end
  for expr in exprs
    e1, e2 = @match expr begin Expr(:call, :(=>), e1, e2) => (e1,e2) end

    if e1 ∈ nameof.(typecons(dom))
      val = e2 isa Symbol ? fromexpr(codom, e2, Ident) : fromexpr(codom, e2, TypeInCtx)
      tyms[fromexpr(dom, e1, Ident)] = val
    else
      val = fromexpr(codom, e2, TermInCtx)
      key = fromexpr(dom, e1, TermInCtx)

      # Check that dom ctx is the same (modulo retagging) with term argcontext
      khead = key.trm.head
      a_c = argcontext(getvalue(dom[khead]))
      Scopes.equiv(key.ctx, a_c) || error("CONTEXT ERROR\n$(key.ctx)\n$a_c")

      trms[khead] = val
    end
  end
  TheoryMap(dom, codom, tyms, trms)
end

macro theorymap(head, body)
  (domname, codomname) = @match head begin
    Expr(:call,:(=>), name, parent) => (name, parent)
    _ => error("could not parse head of @theory: $head")
  end

  dom = macroexpand(__module__, :($domname.@theory))
  codom = macroexpand(__module__, :($codomname.@theory))
  fromexpr(dom, codom, body, TheoryMap)
end

"""Invert a theory iso"""
# Base.inv(::TheoryMap) = error("Not implemented")

end # module
