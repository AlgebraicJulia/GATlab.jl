module TestGATs 

using Gatlab, Test

# GAT ASTs
##########

scope = Scope(:number, :(+), :(*))

number, plus, times = Reference.(idents(scope; name=[:number, :(+), :(*)]))

one = AlgTerm(Constant(1, AlgType(number)))

two = AlgTerm(Constant(2, AlgType(number)))

three = AlgTerm(plus, [one, two])

@test toexpr(scope, three) == :((1::number) + (2::number))

# This throws a type error because it tries to look up `+` with a signature,
# of AlgSorts, but `scope` only has nothing-typed signatures.
@test_throws TypeError fromexpr(scope, toexpr(scope, three), AlgTerm) == three

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

seg = fromexpr(EmptyContext(), seg_expr, GATSegment)

@test toexpr(EmptyContext(), seg) == seg_expr

O, H, i, cmp = idents(seg; lid=LID.(1:4))

# Extend seg with a context of (A: Ob)
sortscope = Scope([Binding{AlgType}(:A, Set([:A]), AlgType(O))])
A = ident(sortscope; name=:A)

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

end # module
