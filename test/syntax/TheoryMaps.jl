module TestTheoryMaps 

using GATlab, GATlab.Stdlib, Test

# Set up 
########

T = ThCategory.Meta.theory
TP = ThPreorder.Meta.theory
TLC = ThLawlessCat.Meta.theory
TM = ThMonoid.Meta.theory
TNP = ThNatPlus.Meta.theory

PC = PreorderCat.MAP
NP = NatPlusMonoid.MAP

# TheoryMaps 
############
x = toexpr(PC)
tm2 = fromexpr(T, TP, x, TheoryMap)
x2 = toexpr(tm2)
@test x == x2

# Validation of putative theory maps 
#-----------------------------------
@test_throws LoadError @eval @theorymap F(ThCategory, ThPreorder) begin
  Ob => default
  Hom => Leq
  compose(f, g) ⊣ [(a,b,c,d)::Ob, f::(a → b), g::(c → d)] => 
    trans(f, g) ⊣ [a,b,c,d, f::Leq(a, b), g::Leq(c, d)] # wrong ctx for compose
  id(a) ⊣ [a::Ob] => refl(a) ⊣ [a]
end

@test_throws LoadError @eval @theorymap F(ThCategory, ThPreorder) begin
  Ob => default
  Hom => Leq
  compose(f, g) ⊣ [(a,b,c)::Ob, f::(a → b), g::(b → c)] => 
    trans(f, g) ⊣ [a, b, c, f::Leq(a, b), g::Leq(b, c)]
  id(a) ⊣ [a::Ob] => refl(a) ⊣ [a, b] # codom has different context
end

@test_throws LoadError @eval @theorymap ThCategory => ThPreorder begin
  Ob => default
  Hom => default # bad type map
  compose(f, g) ⊣ [(a,b,c)::Ob, f::(a → b), g::(b → c)] => 
    trans(f, g) ⊣ [a, b, c, f::Leq(a, b), g::Leq(b, c)]
  id(a) ⊣ [a::Ob] => refl(a) ⊣ [a]
end

@test_throws LoadError @eval @theorymap F(ThCategory, ThPreorder) begin
  Ob => default
  Hom => Leq
  compose(f, g) ⊣ [a::Ob, b::Ob, c::Ob, f::(a → b), g::(b → c)] => 
    trans(f, g) ⊣ [a, b, c, f::Leq(a, b), g::Leq(b, c)]  
  id(b) ⊣ [b::Ob] => refl(a) ⊣ [a] # the LHS doesn't match id's originally defined context
end

# Applying theorymap as a function to Ident and TermInCtx
#--------------------------------------------------------

# Test PreorderCat

((Ob, om), (Hom, Hm)), ((Cmp, cm), (Id, im)) = typecons(T), termcons(T)
((Def, dm), (Leq, lm)), ((Refl, rm), (Tr, tm)) = typecons(TP), termcons(TP)

@test PC(om).val == AlgType(Def, dm)
@test PC(cm).val.body.method == tm

@test PC(getvalue(T[cm]).localcontext) isa TypeScope

@test_throws KeyError PC(dm)

xterm = fromexpr(TM, :(x ⊣ [x]), TermInCtx)
res = NP(xterm)
toexpr(ThNat.Meta.theory, res)

xterm = fromexpr(TM, :(e()⋅(e()⋅x) ⊣ [x]), TermInCtx)
res = NP(xterm)
expected = fromexpr(TNP, :(Z()+(Z()+x) ⊣ [x::ℕ]), TermInCtx)
@test toexpr(TNP, res) == toexpr(TNP, expected)

# Test OpCat

xterm = fromexpr(T, :(id(x) ⋅ p ⋅ q ⋅ id(z) ⊣ [(x,y,z)::Ob, p::Hom(x,y), q::Hom(y,z)]), TermInCtx)
expected = :(compose(id(z), compose(q,  compose(p, id(x)))) ⊣ [x::Ob,y::Ob,z::Ob, p::Hom(y,x), q::Hom(z,y)])
@test toexpr(T, OpCat.MAP(xterm)) == expected


# Check that maps are not sensitive to order of bindings

@theorymap OpCat2(ThCategory, ThCategory) begin
  Ob => Ob
  Hom(foo, bar) ⊣ [foo::Ob, bar::Ob] => Hom(bar, foo)
  id(a) ⊣ [a::Ob] => id(a)
  compose(p,q) ⊣ [(z,y,x)::Ob, q::Hom(y,z), p::Hom(x,y)] => compose(q, p)
end
@test toexpr(T, OpCat2.MAP(xterm)) == expected


# Inclusions 
#############
incl = TheoryIncl(TLC, T)
@test TheoryMaps.dom(incl) == TLC
@test TheoryMaps.codom(incl) == T
incl2 = TheoryIncl(ThGraph.Meta.theory, TLC)
incl3 = TheoryIncl(ThGraph.Meta.theory, T)

@test TheoryMaps.compose(incl2, incl) == incl3

toexpr(incl)
@test_throws ErrorException TheoryIncl(T, TLC)
@test_throws ErrorException inv(incl)

# Identity 
##########
i = IdTheoryMap(T)
@test TheoryMaps.dom(i) == T
@test TheoryMaps.codom(i) == T
@test TheoryMaps.compose(i,i) == i
@test TheoryMaps.compose(incl,i) == incl


end # module
