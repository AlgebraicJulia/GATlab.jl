module TestExprInterop

using Gatlab, Test

bind_x = Binding{String}(:x, Set([:x, :X]), "ex")
bind_y = Binding{String}(:y, Set([:y, :Y]), "why")

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

@test toexpr(c, Reference(x)) == :x!1
@test fromexpr(c, :x!1, Reference) == Reference(x)

@test toexpr(c, Reference()) == :(_)
@test fromexpr(c, :(_), Reference) == Reference()

end
