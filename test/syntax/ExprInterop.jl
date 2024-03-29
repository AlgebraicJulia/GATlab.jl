module TestExprInterop

using GATlab, Test

bind_x = Binding{String}(:x,  "ex")
bind_y = Binding{String}(:y, "why")

scope = Scope([bind_x, bind_y])
x, y = idents(scope; name=[:x, :y])

@test toexpr(scope, x) == :x
@test fromexpr(scope, :x, Ident) == x

scope′ = Scope([bind_x, bind_y])

x′, y′ = idents(scope′; name=[:x, :y])

c = ScopeList([scope, scope′])

@test toexpr(c, x) == :x!1
@test toexpr(c, x′) == :x
@test toexpr(c, Ident(gettag(scope), LID(1))) == :(var"#1!1")
@test toexpr(c, Ident(gettag(scope′), LID(1))) == :(var"#1")

@test fromexpr(c, :x, Ident) == x′
@test fromexpr(c, :x!1, Ident) == x
@test fromexpr(c, :(var"#1!1"), Ident) == x
@test fromexpr(c, :(var"#1"), Ident) == x′

end
