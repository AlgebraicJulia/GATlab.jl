module ParseTests

using Test
using Gatlab

"""
Test whether the @theory macro produces what we expect (manually constructed)
"""


ThSet′ = TheoryExtType(ThEmpty, TypeCon(ThEmpty, :Ob), name="Set")

@test ThSet == ThSet′

HomCtx = Context(
  ThSet′,
  [TermCon(ThSet′, :a, TypeInContext((0,1))), 
   TermCon(ThSet′, :b, TypeInContext((0,1)))],
)

ThGraph′ = TheoryExtType(
    ThSet′,
    TypeCon(HomCtx,:Hom,[(0,1),(0,2)]),
    name="Graph"
)

@test ThGraph == ThGraph′

ComposeCtx1 = Context(
    ThGraph′,
    [TermCon(ThGraph′, :a, TypeInContext((1,1))),  # Ob
     TermCon(ThGraph′, :b, TypeInContext((1,1))),  # Ob
     TermCon(ThGraph′, :c, TypeInContext((1,1)))], # Ob
)
ComposeCtx2 = Context(
  ComposeCtx1,
  [TermCon(ComposeCtx1,:f,TypeInContext((1,1), TermInContext.([(0,1),(0,2)]))), # Hom(A,B)
   TermCon(ComposeCtx1,:g,TypeInContext((1,1), TermInContext.([(0,2),(0,3)])))],# Hom(B,C)
)

ThLawlessCat′ = TheoryExtTerm(
  ThGraph′,
  TermCon(ComposeCtx2,
    Symbol("•"),
    TypeInContext((2,1), TermInContext.([(1,1),(1,3)])), # Hom(A,C)
    [((0,1)),((0,2))]), # (f,g)
    name="LawlessCat"
)

@test ThLawlessCat′ == ThLawlessCat

AscCtx1 = Context(
    ThLawlessCat′,
    [TermCon(ThLawlessCat′, Symbol(x), TypeInContext((2,1))) for x in "αβγδ"], # Ob
)
AscCtx2 = Context(
  AscCtx1,
  [TermCon(AscCtx1, Symbol(f), TypeInContext((2, 1), 
           TermInContext.([(0,i),(0,i+1)]))) 
   for (i,f) in enumerate("ϕψθ")]
)

f,_,h = [TermInContext((0,i)) for i in 1:3]
fg,gh = [TermInContext((2,1),TermInContext.([(0,i),(0,i+1)])) for i in 1:2]
f_gh = TermInContext((2,1), [fg,h])
fg_h = TermInContext((2,1), [f,gh])
hom_ad = TypeInContext((3,1),TermInContext.([(1,1),(1,4)]))
ThAscCat′ = TheoryExtAxiom(ThLawlessCat′,
  Axiom(AscCtx2, :associativity, hom_ad, fg_h, f_gh);
  name="AscCat")

@test ThLawlessCat == ThLawlessCat′

end # module
