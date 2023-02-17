module Theories
export ThSet, HomCtx, ThGraph, ThLawlessCat 
using ..GATs

ThSet = TheoryExtType(
  EmptyTheory(),
  [TypeCon(EmptyTheory(), :Ob, [])],
)


HomCtx = TheoryExtTerm(
  ThSet,
  [TermCon(ThSet, :a, TypeInContext((1,1),[])),
   TermCon(ThSet, :b, TypeInContext((1,1),[]))],
)

ThGraph = TheoryExtType(
  ThSet,
  [TypeCon(HomCtx,:Hom,[(1,1),(1,2)])],
)

ComposeCtx1 = TheoryExtTerm(
  ThGraph,
  [
    TermCon(ThGraph, :a, TypeInContext((2,1),[])),
    TermCon(ThGraph, :b, TypeInContext((2,1),[])),
    TermCon(ThGraph, :c, TypeInContext((2,1),[])),
  ],
)
ComposeCtx2 = TheoryExtTerm(
  ComposeCtx1,
  [
    TermCon(ComposeCtx1,:f, TypeInContext((2,1),
                                          [TermInContext((1,1),[]),TermInContext((1,2),[])])),
    TermCon(ComposeCtx1,:g, TypeInContext((2,1),
                                          [TermInContext((1,2),[]),TermInContext((1,3),[])])),
  ],
)

# TODO
# ThLawlessCat = TheoryExtTerm(
#   ThGraph,
#   [TermConstructor(ComposeCtx2,
#     :compose,
#     TypeInContext((3,1),TermInContext.([(1,2),(1,3)])),
#     TermInContext.([((0,1)),((0,2))]))],
# )

end
