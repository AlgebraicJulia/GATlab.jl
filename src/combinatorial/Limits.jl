module Limits
export pushout, initial, terminal

using ..DataStructs
using ..DataStructs: Idx, NMI, NMIs, NMVIs, ScopedNM, Morphism, Comb, map_nm
using ..CModels
using ..CModels: rand_nm, random_function
using ...Syntax
using ...Stdlib
using ...Models
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
      apex.sets[s] = ScopedNM(rand_nm(apex.sets, T, getcontext(T, s), Int[],[0]), T, s) # apex w/ zeros
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
      apex.funs[s] = ScopedNM(rand_nm(apex.sets, T, getcontext(T, s), Int[], [0]), T, s)
      for bargs in TypeIterator(B[s])
        fbargs = ι₁(bargs)
        apex.funs[s][fbargs] = NMI(getvalue(ι₁(B(bargs))))
      end
      for cargs in TypeIterator(C[s])
        gcargs = ι₂(cargs)
        apex.funs[s][gcargs] = NMI(getvalue(ι₂(C(cargs))))
      end
    end
    return (apex, ι₁, ι₂)
  end
end

# TODO Implement ThPushout

end # module