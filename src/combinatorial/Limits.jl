"""
Currently just colimits.

Rather than a whole reimplementation of the generic (co)limit and diagram 
infrastructure of Catlab, we opt for specific implementations of initial, 
coproduct, and pushout. This could form the starting point for a generic
implementation down the line. 
"""
module Limits
export pushout, initial, terminal, coproduct, oplus, copair

using ..DataStructs
using ..DataStructs: Idx, NMI, NMIs, NMVI, NMVIs, ScopedNM, ScopedNMs,Morphism, 
                     Comb, map_nm, apply_morphism, const_nm
using ..CModels
using ..CModels: empty_function # rand_nm, 
using ...Syntax
using ...Stdlib
using ...Models: @withmodel
using .ThCategory

using DataStructures: IntDisjointSets, find_root!

initial(T::GAT) = CombinatorialModel(T; card_range=0:0)

terminal(T::GAT) = CombinatorialModel(T; card_range=1:1)

"""
Pushout a span B <-f- A -g-> C.

This must be done iteratively for each sort, depending on the earlier sorts.

A colimit of finite GAT models can itself be infinite. So we cannot expect 
`saturate!` to terminate with the result.

With a bit of work this code could be generalized to work on bipartite colimit 
diagrams.
"""
function pushout(f::Morphism, g::Morphism)
  T = gettheory(f)
  @withmodel CombinatorialModelC(T) (dom, codom) begin
    A, B, C = dom(f), codom(f), codom(g)
    A == dom(g) || error("Cannot pushout without common apex")
    apex = initial(T)
    ι₁, ι₂ = Morphism(NMVIs(), B, apex), Morphism(NMVIs(), C, apex)
    
    # Populate cardinality data of apex and populate maps ι₁, ι₂
    for s in sorts(T)
      apex.sets[s] = ScopedNM(empty_function(apex.sets, T, s), T,s)  # apex w/ zeros
      (Bs, Bs⁻¹), (Cs, Cs⁻¹) = map([B=>false,C=>true]) do (X, offset) 
        Xs = collect(TermIterator(X[s]))
        Xs => Dict([v => (i + (offset ? sum(B[s]) : 0)) for (i, v) in enumerate(Xs)])
      end 
      i1, i2 = 1:length(Bs), 1:length(Cs) .+ length(Bs)
      eq = IntDisjointSets(i2.stop)
      for aterm in TermIterator(A[s])
        union!(eq, Bs⁻¹[f(aterm)], Cs⁻¹[g(aterm)])
      end
      roots = find_root!.(Ref(eq), 1:length(eq))
      uroots = unique(roots)
      rootdict = [findfirst(==(i), uroots) for i in 1:length(eq)]
      apex_terms = map(uroots) do eq_idx
        f_id = findfirst(==(eq_idx), i1)
        ι, trm = if !isnothing(f_id)
          (ι₁, Bs[f_id])
        else
          (ι₂, Cs[findfirst(==(eq_idx), i2) - i1.stop])
        end
        typ = ι(argsof(trm))
        add_part!(apex, typ) |> getvalue
      end
      function fun1(idx::Vector{<:Idx}, val::Int)::Vector{Int}
        terms = getindex.(Ref(Bs⁻¹), NestedTerm.(1:val,Ref(NestedType(s, idx))))
        apex_terms[rootdict[roots[i1[terms]]]]
      end 
      ι₁.components[s] = map_nm(fun1, Vector{Int}, B[s]; index=true)
      function fun2(idx::Vector{<:Idx}, val::Int)::Vector{Int}
        terms = getindex.(Ref(Cs⁻¹), NestedTerm.(1:val,Ref(NestedType(s, idx))))
        apex_terms[rootdict[roots[i2[terms]]]]
      end
      ι₂.components[s] = map_nm(fun2, Vector{Int}, C[s]; index=true)
    end
    # Populate function data
    for s in funsorts(T)
      apex.funs[s] = ScopedNM(empty_function(apex.sets, T, s), T, s)
      for bargs in TypeIterator(B[s])
        fbargs = ι₁(bargs)
        bval = B(bargs)
        getvalue(bval) > 0 || continue
        apex.funs[s][fbargs] = NMI(getvalue(ι₁(bval)))
      end
      for cargs in TypeIterator(C[s])
        gcargs = ι₂(cargs)
        apex.funs[s][gcargs] = NMI(getvalue(ι₂(C(cargs))))
      end
    end
    ι₁.dom == B || error("Bad i1")
    ι₂.dom == C || error("Bad i2")
    return (apex, ι₁, ι₂)
  end
end

"""
Coproduct of (non-empty) list of models.
"""
function coproduct(Xs::Vector{Comb})
  M = first(Xs)
  T = gettheory(M)
  res = initial(T)
  comps = [ScopedNMs(T, Dict{AlgSort, NMVI}()) => X for X in Xs]
  for s in sorts(T)
    res[s] = empty_function(res.sets, T, s)
    for (comp, X) in comps
      function fun(idx::Vector{<:Idx}, v::Int)::Vector{Int}
        nm = res[s][apply_morphism(T, comp, NestedType(s,idx))]
        vec = (1:v) .+ getvalue(nm)
        nm.data = getvalue(nm) + v
        collect(vec)
      end
      comp[s] = map_nm(fun, Vector{Int}, X[s]; index=true)
    end
  end
  for s in funsorts(T)
    res[s] = empty_function(res.sets, T, s)
    for (comp, X) in comps
      for args in TypeIterator(X[s])
        res[apply_morphism(T, comp, args)] = NMI(getvalue(apply_morphism(T, comp, X(args))))
      end
    end
  end
  [Morphism(comp, X, res) for (comp, X)  in comps]
end


"""
Take a nonempty collection of maps Aᵢ → B and make a single map ΣA → B
"""
function copair(vs::Vector{Morphism})
  ι = coproduct([v.dom for v in vs])
  all([v.codom == first(vs).codom for v in vs]) || error("Cannot copair")
  dom, codom = [first(x).codom for x in [ι, vs]]
  comps = Dict(map(sorts(gettheory(dom))) do s 
    res = const_nm(getvalue(dom[s]), Int[]; copy=true, type=Vector{Int})
    for (i,v) in zip(ι, vs)
      for (idx, mapping) in v[s]
        append!(getvalue(res[i(NestedType(s, idx))]), mapping)
      end
    end
    s => res
  end)
  res = Morphism(comps, dom, codom)
  is_natural(res) || error("unnatural")
  res
end

"""
Take a nonempty collection of maps Aᵢ → Bᵢ and make a single map ΣA → ΣB
"""
function oplus(vs::Vector{Morphism})
  Aι  = coproduct([v.dom for v in vs])
  Bι = coproduct([v.codom for v in vs])
  dom, codom = [first(x).codom for x in [Aι, Bι]]
  comps = Dict(map(sorts(gettheory(dom))) do s 
    res = const_nm(getvalue(dom[s]), Int[]; copy=true, type=Vector{Int})
    for (Ai, v, Bi) in zip(Aι, vs, Bι)
      for (idx, mapping) in v[s]
        A_args = NestedType(s, idx)
        mapping′ = Bi.(v.(NestedTerm.(1:length(mapping), Ref(A_args))))
        append!(getvalue(res[Ai(A_args)]), getvalue.(mapping′))
      end
    end
    s => res
  end)
  res = Morphism(comps, dom, codom)
  is_natural(res) || error("unnatural")
  res
end


# TODO Implement ThPushout for CombinatorialModelC

end # module