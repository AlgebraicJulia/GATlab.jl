module TestVisualization
using Gatlab


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
fg,gh = [TermInContext((2,1),TermInContext.([(0,i),(1,i+1)])) for i in 1:2]
f_gh = TermInContext((2,1), [fg,h])
fg_h = TermInContext((2,1), [f,gh])
hom_ad = TypeInContext((3,1),TermInContext.([(1,1),(1,4)]))
ThAscCat = TheoryExtAxiom(ThLawlessCat,Axiom(AscCtx2, :associativity, hom_ad, fg_h, f_gh))


end # module 