module TestGATs 

using GATlab, Test

# GAT ASTs
##########

function basicprinted(x)
  sprint(show, x; context=(:color=>false))
end

scope = Scope(:number, :(+), :(*))

number, plus, times = idents(scope; name=[:number, :(+), :(*)])

one = AlgTerm(Constant(1, AlgType(number)))

two = AlgTerm(Constant(2, AlgType(number)))

three = AlgTerm(plus, [one, two])

@test toexpr(scope, three) == :((1::number) + (2::number))

@test fromexpr(TypeScope(), two.head, AlgTerm) == two
@test_throws Exception fromexpr(TypeScope(), :(x = 3), AlgTerm)

@test basicprinted(two) == "AlgTerm(2::number)"

@test_throws Exception AlgSort(scope, three)

@test sortcheck(scope, two) == AlgSort(number)

@test_throws Exception sortcheck(scope, three)

@test_throws Exception AlgSort(scope, three)

# This throws a type error because it tries to look up `+` with a signature,
# of AlgSorts, but `scope` only has nothing-typed signatures.
@test_throws TypeError fromexpr(scope, toexpr(scope, three), AlgTerm)

seg_expr = quote
  Ob :: TYPE
  Hom(dom::Ob, codom::Ob) :: TYPE
  id(a::Ob) :: Hom(a,a)
  compose(f::Hom(a, b), g::Hom(b, c)) :: Hom(a, c) ⊣ [a::Ob, b::Ob, c::Ob]
  ((compose(f, compose(g, h)) == compose(compose(f, g), h)) :: Hom(a,d)) ⊣ [
    a::Ob, b::Ob, c::Ob, d::Ob,
    f::Hom(a, b), g::Hom(b, c), h::Hom(c, d)
  ]
end

seg = fromexpr(TypeScope(), seg_expr, GATSegment)

@test toexpr(TypeScope(), seg) == seg_expr

O, H, i, cmp = getidents(seg)

# Extend seg with a context of (A: Ob)
sortscope = Scope([Binding{AlgType}(:A, AlgType(O))])
A = ident(sortscope; name=:A)
ATerm = AlgTerm(A)


ss = AppendScope(ScopeList([seg]), sortscope)
@test sortcheck(ss, AlgTerm(A)) == AlgSort(O)

# # Good term and bad term
ida = fromexpr(ss, :(id(A)), AlgTerm)
iida = AlgTerm(i,[AlgTerm(i, [AlgTerm(A)])])

@test AlgSort(ss, ida) == AlgSort(H)
@test sortcheck(ss, ida) == AlgSort(H)
@test AlgSort(ss, iida) == AlgSort(H)
@test_throws Exception sortcheck(ss, iida)

# Good type and bad type
haa = AlgType(H,[AlgTerm(A),AlgTerm(A)])
haia = AlgType(H,[AlgTerm(A),ida])
@test sortcheck(ss, haa)
@test_throws Exception sortcheck(ss, haia)

# Renaming 
BTerm = rename(gettag(sortscope), Dict(:A=>:B), ATerm)
Bsortscope = Scope([Binding{AlgType}(:B, AlgType(O))]; tag=gettag(sortscope))
BTerm_expected = AlgTerm(ident(Bsortscope;name=:B))
@test BTerm == BTerm_expected

# Subset 
#-------
T = ThCategory.THEORY
TG = ThGraph.THEORY
@test TG ⊆ T
@test T ⊈ TG

# InCtx
#----------
tic = fromexpr(T, :(compose(f,compose(id(b),id(b))) ⊣ [a::Ob, b::Ob, f::Hom(a,b)]), TermInCtx);
tic2 = fromexpr(T,toexpr(T, tic), TermInCtx) # same modulo scope tags


typic = fromexpr(T, :(Hom(a,b) ⊣ [a::Ob, b::Ob, f::Hom(a,b)]), TypeInCtx)
typic2 = fromexpr(T,toexpr(T, typic), TypeInCtx) # same modulo scope tags

# Type inference 
#---------------

t = fromexpr(T,:(id(x)⋅(p⋅q) ⊣ [(x,y,z)::Ob, p::Hom(x,y), q::Hom(y,z)]), TermInCtx)
expected = fromexpr(AppendScope(T, t.ctx), :(Hom(x,z)), AlgType)
@test Syntax.GATs.infer_type(T, t) == expected

end # module
