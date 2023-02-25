module TestGATs 

using Test
using Gatlab

Emp = Judgment[]
ThSet = Theory("ThSet", [Judgment("Ob",[],TypeCon())])
ThGrph = extend(ThSet, "ThGraph",
  [
      Judgment(
      "Hom",
      [
        Judgment("a", [], TermCon(Typ(1))),
        Judgment("b", [], TermCon(Typ(2)))
      ],
      TypeCon([2,1])
    )
  ]
)

ThLawlessCat = extend(ThGrph, "LawlessCat", [
  Judgment(
    "⋅",
    [Judgment("a",[],TermCon(Typ(2))),
     Judgment("b",[],TermCon(Typ(3))),
     Judgment("c",[],TermCon(Typ(4))),
     Judgment("f",[],TermCon(Typ(4,Trm.([3,2])))),
     Judgment("g",[],TermCon(Typ(5,Trm.([3,2]))))],
     TermCon(Typ(5,Trm.([4,2])), [1,0])
  )
])



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

# LawlessCat->Preorder
f0 = EmptyTheoryHom(ThPreorder);
f1 = TheoryHomExt(f0, ThSet, ThPreorder,[(4,1)]);
f2 = TheoryHomExt(f1, ThGraph, ThPreorder, [(3,1)]);
f = TheoryHomExt(f2, ThLawlessCat, ThPreorder, [],
                 [TermInContext((1,1),TermInContext.([(0,1),(0,2)]))]);
cX0 = Context(ThLawlessCat)
cX1 = Context(
  cX0,
  [TermCon(cX0, :a, TypeInContext((2,1))), 
   TermCon(cX0, :b, TypeInContext((2,1)))],
)
cX2 = Context(cX1, 
  [TermCon(cX1, :f, 
    TypeInContext((2,1),
      TermInContext.([(0,1),(0,2)])))])

cY0 = add_term(Context(ThPreorder), TypeInContext((4,1)),:A);

# f(cX2) # PUSHING FORWARD OVER THEORY HOMS IS CURRENTLY BROKEN

cXtst = add_term(Context(ThLawlessCat), TypeInContext((2,1)),:P);
cYtst = add_term(Context(ThPreorder), TypeInContext((4,1)),:Q);

tic = TermInContext((1,1),TermInContext.([(0,1),(0,1)]))
show_term(cXtst, tic)

ftic = f(cXtst,cYtst,tic)
show_term(cYtst, ftic)

# monoid swap 
f0 = EmptyTheoryHom(ThMonoid);
f1 = TheoryHomExt(f0, ThSet, ThMonoid,[(5,1)]);
swp = TermInContext((4,1),TermInContext.([(0,2),(0,1)])) # 
f2 = TheoryHomExt(f1, ThMagma, ThMonoid,[],[swp]);
f3 = TheoryHomExt(f2, ThSemiGroup, ThMonoid);
f4 = TheoryHomExt(f3, parent(ThMonoid,2), ThMonoid,[],[TermInContext((2,1))]);
f5 = TheoryHomExt(f4, parent(ThMonoid), ThMonoid);
f  = TheoryHomExt(f5, ThMonoid, ThMonoid);



# @instance NatPlusIsMonoid{ThMonoid, ThNatPlus}
#   Ob = ℕ
#   ∘(x, y) = x + y
#   e() = Z() 
# end

@theory ThX <: ThEmpty begin
  X::TYPE ⊣ []
end
f0 = EmptyTheoryHom(ThX);
f = TheoryHomExt(f0, ThSet, ThX,[(0,1)]);
Sctx = Context(ThSet,TermCon(ThSet,:q,TypeInContext((0,1))))




# There are finer grained theories in between these!
f0 = EmptyTheoryHom(ThNatPlus);
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