module Theories
export ThSet, ThGraph, ThLawlessCat 
using ..GATs 

ThSet = TheoryExtType(
    EmptyTheory(),
    TypeCon(EmptyTheory(), :Ob, []),
    name="Set"
)


HomCtx = TheoryExtTerm(
  ThSet,
  [TermCon(ThSet, :a, TypeInContext((0,1),[])), 
   TermCon(ThSet, :b, TypeInContext((0,1),[]))],
)

ThGraph = TheoryExtType(
    ThSet,
    TypeCon(HomCtx,:Hom,[(0,1),(0,2)]),
    name="Graph"
)

ComposeCtx1 = TheoryExtTerm(
    ThGraph,
    [TermCon(ThGraph, :a, TypeInContext((1,1))),  # Ob
     TermCon(ThGraph, :b, TypeInContext((1,1))),  # Ob
     TermCon(ThGraph, :c, TypeInContext((1,1))),],# Ob
)
ComposeCtx2 = TheoryExtTerm(
  ComposeCtx1,
  [TermCon(ComposeCtx1,:f,TypeInContext((1,1), TermInContext.([(0,1),(0,2)]))), # Hom(A,B)
   TermCon(ComposeCtx1,:g,TypeInContext((1,1), TermInContext.([(0,2),(0,3)])))],# Hom(B,C)
)

ThLawlessCat = TheoryExtTerm(
  ThGraph,
  TermCon(ComposeCtx2,
    Symbol("•"),
    TypeInContext((2,1), TermInContext.([(1,2),(1,3)])), # Hom(A,C)
    [((0,1)),((0,2))]), # (f,g)
    name="LawlessCat"
)


end
