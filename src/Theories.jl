module Theories

ThSet = TheoryExt(
    EmptyTheory(),
    [TypeConstructor(EmptyTheory, :Ob, [])],
    [],
    []
)


HomCtx = TheoryExt(
  ThSet,
  [],
  [TermConstructor(ThSet, :a, [], TypeInContext((1,1),[])), 
   TermConstructor(ThSet, :b, [], TypeInContext((1,1),[]))],
  []
)

ThGraph = TheoryExt(
    ThSet,
    [TypeConstructor(HomCtx,:Hom,[(1,1),(1,2)])],
    [],
    []
)

ComposeCtx1 = TheoryExt(
    ThGraph,
    [],
    [
        TermConstructor(ThGraph, :a, [], TypeInContext((2,1),[])),
        TermConstructor(ThGraph, :b, [], TypeInContext((2,1),[])),
        TermConstructor(ThGraph, :c, [], TypeInContext((2,1),[])),
    ],
    []
)
ComposeCtx2 = TheoryExt(
  ComposeCtx1,
  [],
  [
    TermConstructor(ComposeCtx1,:f,[],TypeInContext((2,1), 
                    [TermInContext((1,1),[]),TermInContext((1,2),[])])),
    TermConstructor(ComposeCtx1,:g,[],TypeInContext((2,1), 
                    [TermInContext((1,2),[]),TermInContext((1,3),[])])),
  ],
  []
)

ThLawlessCat = TheoryExt(
  ThGraph,
  [],
  [TermConstructor(ComposeCtx2,:compose,[(0,2),(0,1)])],
  []
)

end