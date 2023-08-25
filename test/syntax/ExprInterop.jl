module TestExprInterop

using Gatlab, Test

bind_x = Binding{String}(:x, Set([:x, :X]), "ex")
bind_y = Binding{String}(:y, Set([:y, :Y]), "why")

scope = Scope([bind_x, bind_y])
x, y = idents(scope, [:x, :Y])

c = ScopeList([scope])

@test toexpr(c, x) == :x
@test fromexpr(c, :x, Ident) == x

scope′ = Scope([bind_x, bind_y])
x′, y′ = idents(scope′, [:x, :Y])

c = ScopeList([scope, scope′])

@test toexpr(c, x) == :x!1
@test toexpr(c, x′) == :x
@test toexpr(c, Ident(gettag(scope), 1)) == :(var"#1!1")
@test toexpr(c, Ident(gettag(scope′), 1)) == :(var"#1")

@test fromexpr(c, :x, Ident) == x′
@test fromexpr(c, :x!1, Ident) == x
@test fromexpr(c, :(var"#1!1"), Ident) == x
@test fromexpr(c, :(var"#1"), Ident) == x′

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

seg = fromexpr(c, seg_expr, GATSegment)

@test toexpr(c, seg) == seg_expr

O, H, i, cmp = idents(seg, 1:4)

# Extend seg with a context of (A: Ob)
sortscope = Scope([Binding{AlgType}(:A, Set([:A]), AlgType(O))])
A = ident(sortscope, :A)

ss = AppendScope(ScopeList([seg]), sortscope)
sortcheck(ss, AlgTerm(A))

# Good term and bad term
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

end
