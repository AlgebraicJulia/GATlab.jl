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

end