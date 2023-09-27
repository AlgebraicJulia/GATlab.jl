module TestTheoryMaps 

using GATlab
using Test

# Set up 
########

T = ThCategory.THEORY
TP = ThPreorder.THEORY
TLC = ThLawlessCat.THEORY
TM = ThMonoid.THEORY
TNP = ThNatPlus.THEORY

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

(Ob, Hom), (Cmp, Id) = typecons(T), termcons(T)
@test PC(Ob).trm == AlgType(ident(TP; name=:default))
@test PC(Cmp) isa TermInCtx

@test PC(getvalue(T[Cmp]).localcontext) isa TypeScope

@test_throws KeyError PC(first(typecons(TP)))

xterm = fromexpr(TM, :(x ⊣ [x]), TermInCtx)
res = NP(xterm)
toexpr(ThNat.THEORY, res)

xterm = fromexpr(TM, :(e⋅(e⋅x) ⊣ [x]), TermInCtx)
res = NP(xterm)
expected = fromexpr(TNP, :(Z+(Z+x) ⊣ [x::ℕ]), TermInCtx)
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
incl2 = TheoryIncl(ThGraph.THEORY, TLC)
incl3 = TheoryIncl(ThGraph.THEORY, T)

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
