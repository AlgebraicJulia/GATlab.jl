module Theories
export ThSet, ThGraph, ThLawlessCat, ThAscCat
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
    TypeInContext((2,1), TermInContext.([(1,1),(1,3)])), # Hom(A,C)
    [((0,1)),((0,2))]), # (f,g)
    name="LawlessCat"
)


# Associativity 
#---------------
AscCtx1 = TheoryExtTerm(
    ThLawlessCat,
    [TermCon(ThLawlessCat, x, TypeInContext((2,1))) for x in [:a,:b,:c,:d]], # Ob
)
AscCtx2 = TheoryExtTerm(
  AscCtx1,
  [TermCon(AscCtx1, Symbol(f), TypeInContext((2, 1), 
           TermInContext.([(0,i),(0,i+1)]))) 
   for (i,f) in enumerate("fgh")]
)

f,_,h = [TermInContext((0,i)) for i in 1:3]
fg,gh = [TermInContext((2,1),TermInContext.([(0,i),(0,i+1)])) for i in 1:2]
f_gh = TermInContext((2,1), [fg,h])
fg_h = TermInContext((2,1), [f,gh])
hom_ad = TypeInContext((3,1),TermInContext.([(1,1),(1,4)]))
ThAscCat = TheoryExtAxiom(ThLawlessCat,
  Axiom(AscCtx2, :associativity, hom_ad, fg_h, f_gh);
  name="AscCat")

end
