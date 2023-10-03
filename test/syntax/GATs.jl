module TestGATs 

using GATlab, Test

# GAT ASTs
##########

function basicprinted(x)
  sprint(show, x; context=(:color=>false))
end

scope = Scope(:number, :(+), :(_), :(*))

number, plus, plusmethod, times = idents(scope; name=[:number, :(+), :(_), :(*)])

one = AlgTerm(Constant(1, AlgType(number)))

two = AlgTerm(Constant(2, AlgType(number)))

three = AlgTerm(plus, plusmethod, [one, two])

@test toexpr(scope, three) == :((1::number) + (2::number))

@test fromexpr(GATContext(GAT(:Empty), TypeScope()), two.body, AlgTerm) == two

@test basicprinted(two) == "AlgTerm(2::number)"

@test_throws Exception AlgSort(scope, three)

@test sortcheck(scope, two) == AlgSort(number)

@test_throws Exception sortcheck(scope, three)

@test_throws Exception AlgSort(scope, three)

@test_throws MethodError fromexpr(scope, toexpr(scope, three), AlgTerm)

seg_expr = quote
  Ob :: TYPE
  Hom(dom, codom) :: TYPE ⊣ [dom::Ob, codom::Ob]
  id(a) :: Hom(a, a) ⊣ [a::Ob]
  compose(f, g) :: Hom(a, c) ⊣ [a::Ob, b::Ob, c::Ob, f::Hom(a, b), g::Hom(b, c)]
  compose(f, compose(g, h)) == compose(compose(f, g), h) :: Hom(a,d) ⊣ [
    a::Ob, b::Ob, c::Ob, d::Ob,
    f::Hom(a, b), g::Hom(b, c), h::Hom(c, d)
  ]
end

thcat = fromexpr(GAT(:ThCat), seg_expr, GAT)

O, H, i, cmp = idents(thcat; name=[:Ob, :Hom, :id, :compose])

ObT = fromexpr(GATContext(thcat), :Ob, AlgType)
ObS = AlgSort(ObT)

# Extend seg with a context of (A: Ob)
sortscope = TypeScope(:A => ObT)

A = ident(sortscope; name=:A)

ATerm = AlgTerm(A)

c = GATContext(thcat, sortscope)

HomT = fromexpr(c, :(Hom(A, A)), AlgType)
HomS = AlgSort(HomT)

@test sortcheck(c, AlgTerm(A)) == ObS

# # Good term and bad term
ida = fromexpr(c, :(id(A)), AlgTerm)

im = ida.body.method

iida = AlgTerm(i, im, [AlgTerm(i, im, [AlgTerm(A)])])

@test AlgSort(c, ida) == HomS
@test sortcheck(c, ida) == HomS
@test AlgSort(c, iida) == HomS
@test_throws Exception sortcheck(c, iida)

# Good type and bad type
haa = HomT
haia = AlgType(HomS.head, HomS.method, [ATerm, ida])
@test sortcheck(c, haa)
@test_throws Exception sortcheck(c, haia)

# Renaming 
BTerm = rename(gettag(sortscope), Dict(:A=>:B), ATerm)
Bsortscope = TypeScope([Binding{AlgType}(:B, ObT)]; tag=gettag(sortscope))
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
