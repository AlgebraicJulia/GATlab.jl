module TestGATs 

using GATlab, Test


# GAT ASTs
##########

function basicprinted(x)
  sprint(show, x; context=(:color=>false))
end

scope = Scope(:number, :(+), :(_), :(*))

number, plus, plusmethod, times = idents(scope; name=[:number, :(+), :(_), :(*)])

one = AlgTerm(Constant(1, AlgType(number, number, AlgTerm[])))

two = AlgTerm(Constant(2, AlgType(number, number, AlgTerm[])))

three = AlgTerm(plus, plusmethod, [one, two])

@test toexpr(scope, three) == :((1::number) + (2::number))

@test fromexpr(GAT(:Empty), two.body, AlgTerm) == two

@test basicprinted(two) == "AlgTerm(2::number)"

@test_throws Exception AlgSort(scope, three)

@test sortcheck(scope, two) == AlgSort(number, number)

@test_throws Exception sortcheck(scope, three)

@test_throws Exception AlgSort(scope, three)

@test_throws MethodError fromexpr(scope, toexpr(scope, three), AlgTerm)

seg_expr = quote
  Ob :: TYPE
  Hom(dom, codom) :: TYPE ⊣ [dom::Ob, codom::Ob]
  id(a) :: Hom(a, a) ⊣ [a::Ob]
  compose(f, g) :: Hom(a, c) ⊣ [a::Ob, b::Ob, c::Ob, f::Hom(a, b), g::Hom(b, c)]
  compose(f, compose(g, h)) == compose(compose(f, g), h) ⊣ [
    a::Ob, b::Ob, c::Ob, d::Ob,
    f::Hom(a, b), g::Hom(b, c), h::Hom(c, d)
  ]
  struct Span(dom::Ob, codom::Ob)
    apex::Ob
    left::Hom(apex, dom)
    right::Hom(apex, codom)
  end
  id_span(x) := Span(x, id(x),id(x)) ⊣ [x::Ob]
end


thcat = fromexpr(GAT(:ThCat), seg_expr, GAT; current_module=[:Foo, :Bar])

O, H, i = idents(thcat; name=[:Ob, :Hom, :id])

ob_decl = getvalue(thcat[O])

ObT = fromexpr(thcat, :Ob, AlgType)
ObS = AlgSort(ObT)
@test toexpr(GATContext(thcat), ObS) == :Ob


# Extend seg with a context of (A: Ob)
sortscope = TypeScope(:A => ObT)

A = ident(sortscope; name=:A)

ATerm = AlgTerm(A)

c = GATContext(thcat, sortscope)

HomT = fromexpr(c, :(Hom(A, A)), AlgType)

AA = :(A == A)
eqA = fromexpr(c, AA, AlgType)
@test toexpr(c, eqA) == AA

HomS = AlgSort(HomT)

@test rename(gettag(sortscope), Dict(:A=>:Z), HomT) isa AlgType
@test retag(Dict(gettag(sortscope)=>newscopetag()), HomT) isa AlgType

@test sortcheck(c, AlgTerm(A)) == ObS

x = fromexpr(c, :(id_span(A)), AlgTerm)
@test sortcheck(c, x) isa AlgSort

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
T = ThCategory.Meta.theory
TG = ThGraph.Meta.theory
@test TG ⊆ T
@test T ⊈ TG

# ToExpr
#-------
toexpr.(Ref(T), T.segments)

# @theory
#########
@theory ThI2 <: ThCategory begin
  square(x) := f⋅f ⊣ [x::Ob, f::Hom(x,x)]
end

@theory ThSpan <: ThCategory begin
  struct Span(dom::Ob, codom::Ob)
    apex::Ob
    left::Hom(apex, dom)
    right::Hom(apex, codom)
  end
  id_span(x) := Span(x, id(x),id(x)) ⊣ [x::Ob]
end



end # module
