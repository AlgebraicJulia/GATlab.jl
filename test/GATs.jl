module TestGATs 

using Test
using Gatlab

# Adding depth to terms in context
fg = TypeInContext((2,1),TermInContext.([(0,1),(0,2)]))
@test fg + 1 == TypeInContext((3,1),TermInContext.([(1,1),(1,2)]))

# Parent 
@test parent(ThGraph,1) == parent(ThGraph) == ThSet
@test parent(ThGraph, 2) == ThEmpty == parent(ThEmpty, 0)

# Constructor checking the contexts. 

# ThGraph is not valid context for an extension to ThSet 
# (b/c ThGraph does not only add nullary term constructors to ThSet)
@test_throws ErrorException TheoryExtType(ThSet, TypeCon(ThGraph, :Hom))

Th2Set = TheoryExtType(ThEmpty, [TypeCon(ThEmpty, :O1), TypeCon(ThEmpty, :O2)])

# ThGraph is not valid context for an extension to ThSet (b/c Th2Set ≰ ThGraph)
@test_throws ErrorException TheoryExtType(Th2Set, TypeCon(ThGraph, :Hom))


end # module 