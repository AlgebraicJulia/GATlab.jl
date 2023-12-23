module Limits

using ..DataStructs
using ..CModels
using ...Syntax

initial(T::GAT) = CombinatorialModel(T; card_range=0:0)
terminal(T::GAT) = CombinatorialModel(T; card_range=1:1)

"""
Pushout a span B <-f- A -g-> C. This is a stub for a function that will be written.

This must be done iteratively for each sort, depending on the earlier sorts.

A colimit of finite GAT models can itself be infinite. So we cannot expect 
`saturate!` to terminate with the result.
"""
function pushout(f::CombinatorialModelMorphism, g::CombinatorialModelMorphism)
  T = gettheory(f)
  C = CombinatorialModelC(T)
  A, B, C = dom[C](f), codom[C](f), codom[C](g)
  A == dom[C](g) || error("Cannot pushout without common apex")
  ι1, ι2 = NMVIs(), NMVIs()
  init = NMIs()
  for s in sorts(T)
    init[s] = random_nm(init, T, getcontext(T, s),Int[],[0]) # initialize w/ zeros
    for (idx, _) in init[s]
      error("NotImplementedYet $s: $idx")
    end
  end

  for s in funsorts(s)
    error("NotImplementedYet $s")
    init[s] = NestedMatrix()
  end
  apex = CombinatorialModel(T; init)
  (apex, Morphism(ι1, B, apex), Morphism(ι2, C, apex))
end

# TODO Implement ThPushout

end # module