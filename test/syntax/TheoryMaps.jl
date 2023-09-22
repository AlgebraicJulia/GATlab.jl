module TestTheoryMaps 

using GATlab
using Test

# Set up 
########

T = ThCategory.THEORY
T2 = ThPreorder.THEORY

# TheoryMaps 
############
x = toexpr(PreorderCat)
tm2 = fromexpr(T, T2, x, TheoryMap)
x2 = toexpr(tm2)
@test x == x2

# Validation of putative theory maps 
#-----------------------------------
@test_throws LoadError @eval @theorymap ThCategory => ThPreorder begin
  Ob => default
  Hom => Leq
  compose(f, g) ⊣ [(a,b,c,d)::Ob, f::(a → b), g::(c → d)] => 
    trans(f, g) ⊣ [a,b,c,d, f::Leq(a, b), g::Leq(c, d)] # wrong ctx for compose
  id(a) ⊣ [a::Ob] => refl(a) ⊣ [a]
end

@test_throws LoadError @eval @theorymap ThCategory => ThPreorder begin
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

@test_throws LoadError @eval @theorymap ThCategory => ThPreorder begin
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
@test PreorderCat(Ob).trm == AlgType(ident(T2; name=:default))
@test PreorderCat(Cmp) isa TermInCtx

@test PreorderCat(argcontext(getvalue(T[Cmp]))) isa TypeScope

@test_throws KeyError PreorderCat(first(typecons(T2)))

xterm = fromexpr(ThMonoid.THEORY, :(x ⊣ [x]), TermInCtx)
res = NatPlusMonoid(xterm)
toexpr(ThNat.THEORY, res)

xterm = fromexpr(ThMonoid.THEORY, :(e⋅(e⋅x) ⊣ [x]), TermInCtx)
res = NatPlusMonoid(xterm)
expected = fromexpr(ThNatPlus.THEORY, :(Z+(Z+x) ⊣ [x::ℕ]), TermInCtx)
@test toexpr(ThNatPlus.THEORY, res) == toexpr(ThNatPlus.THEORY, expected)

# Test OpCat

xterm = fromexpr(T, :(id(x) ⋅ p ⋅ q ⋅ id(z) ⊣ [(x,y,z)::Ob, p::Hom(x,y), q::Hom(y,z)]), TermInCtx)
expected = :(compose(id(z), compose(q,  compose(p, id(x)))) ⊣ [x::Ob,y::Ob,z::Ob, p::Hom(y,x), q::Hom(z,y)])
@test toexpr(T, OpCat(xterm)) == expected


# Inclusions 
#############
TLC = ThLawlessCat.THEORY
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
