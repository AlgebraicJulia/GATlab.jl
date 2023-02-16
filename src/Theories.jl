module Theories
export ThSet, HomCtx, ThGraph, ThLawlessCat 
using ..Core 

ThSet = TheoryExtType(
    EmptyTheory(),
    [TypeConstructor(EmptyTheory(), :Ob, [])],
)


HomCtx = TheoryExtTerm(
  ThSet,
  [TermConstructor(ThSet, :a, TypeInContext((1,1),[])), 
   TermConstructor(ThSet, :b, TypeInContext((1,1),[]))],
)

ThGraph = TheoryExtType(
    ThSet,
    [TypeConstructor(HomCtx,:Hom,[(1,1),(1,2)])],
)

ComposeCtx1 = TheoryExtTerm(
    ThGraph,
    [
        TermConstructor(ThGraph, :a, TypeInContext((2,1),[])),
        TermConstructor(ThGraph, :b, TypeInContext((2,1),[])),
        TermConstructor(ThGraph, :c, TypeInContext((2,1),[])),
    ],
)
ComposeCtx2 = TheoryExtTerm(
  ComposeCtx1,
  [
    TermConstructor(ComposeCtx1,:f, TypeInContext((2,1), 
                    [TermInContext((1,1),[]),TermInContext((1,2),[])])),
    TermConstructor(ComposeCtx1,:g, TypeInContext((2,1), 
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