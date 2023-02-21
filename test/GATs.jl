module TestGATs 

using Test
using Gatlab
using Gatlab.GATs: EmptyTheoryHom,TheoryHomExt

# Adding depth to terms in context
#---------------------------------
fg = TypeInContext((2,1),TermInContext.([(0,1),(0,2)]))
@test fg + 1 == TypeInContext((3,1),TermInContext.([(1,1),(1,2)]))

# Parent 
#-------
@test parent(ThGraph,1) == parent(ThGraph) == ThSet
@test parent(ThGraph, 2) == ThEmpty == parent(ThEmpty, 0)

# Constructor checking the contexts. 
#-----------------------------------

# ThGraph is not valid context for an extension to ThSet 
# (b/c ThGraph does not only add nullary term constructors to ThSet)
@test_throws ErrorException TheoryExtType(ThSet, TypeCon(ThGraph, :Hom))

Th2Set = TheoryExtType(ThEmpty, [TypeCon(ThEmpty, :O1), TypeCon(ThEmpty, :O2)])

# ThGraph is not valid context for an extension to ThSet (b/c Th2Set ≰ ThGraph)
@test_throws ErrorException TheoryExtType(Th2Set, TypeCon(ThGraph, :Hom))


# Morphisms
###########

# @instance NatPlusIsMonoid{ThMonoid, ThNatPlus}
#   Ob = ℕ
#   ∘(x, y) = x + y
#   e() = Z() 
# end

# There are finer grained theories in between these!
f0 = EmptyTheoryHom(ThNatPlus)
f1 = TheoryHomExt(f0, ThSet, ThNatPlus,[(1,1)]);

plus_trm = TermInContext((1,1),TermInContext.([(0,1),(0,2)])) # 

f2 = TheoryHomExt(f1, ThMagma, ThNatPlus,[],[plus_trm]);
f3 = TheoryHomExt(f2, ThSemiGroup, ThNatPlus);
f4 = TheoryHomExt(f3, parent(ThMonoid,2), ThNatPlus,[],[TermInContext((2,1))]);
f5 = TheoryHomExt(f4, parent(ThMonoid), ThNatPlus);
f  = TheoryHomExt(f5, ThMonoid, ThNatPlus);

mctx = Context(ThMonoid,TermCon(ThMonoid,:q,TypeInContext((5,1))))
# res = f(mctx) # ERROR NOT YET WORKING

end # module 