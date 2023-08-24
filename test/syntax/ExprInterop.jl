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

@test fromexpr(ScopeList(), 1, AlgTerm) == AlgTerm(Constant(1))
@test fromexpr(c, :x, AlgTerm) == AlgTerm(x′)
@test fromexpr(c, :(x(y(x))), AlgTerm) == AlgTerm(x′,[AlgTerm(y′,[AlgTerm(x′)])])
@test_throws Exception fromexpr(ScopeList(), quote end, AlgTerm)
@test_throws Exception fromexpr(ScopeList(), 1, AlgType)

term_constructor_expr = :(compose(f::x(a,b), g::y(b,a)) :: Y ⊣ [a::X, b::Y])

term_constructor = fromexpr(c, term_constructor_expr, JudgmentBinding)

@test toexpr(c, term_constructor) == term_constructor_expr

type_constructor_expr = :(Hom(dom::X(foo), codom::Y) :: TYPE ⊣ [foo::Y])

type_constructor = fromexpr(c, type_constructor_expr, JudgmentBinding)

@test toexpr(c, type_constructor) == type_constructor_expr

axiom_expr = :((X(x,a) == Y(y,b)) :: Y ⊣ [a::X, b::Y])

axiom = fromexpr(c, axiom_expr, JudgmentBinding)

@test toexpr(c, axiom) == axiom_expr

seg_expr = quote
  Ob :: TYPE
  Hom(dom::Ob, codom::Ob) :: TYPE
  id(a::Ob) :: Hom(a,a)
  compose(f::Hom(a, b), g::Hom(b, c)) :: Hom(a, c) ⊣ [a::Ob, b::Ob, c::Ob]
end

seg = fromexpr(c, seg_expr, GATSegment)

@test toexpr(c, seg) == seg_expr

end
