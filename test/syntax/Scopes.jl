module TestScopes

using Test, Gatlab

# Ident 

tag = newscopetag()

x = Ident(tag, 1, :x)

@test gettag(x) == tag
@test getlevel(x) == 1
@test nameof(x) == :x
@test repr(x) == "x"

nameless = Ident(tag, 1, nothing)

@test repr(nameless) == "#1"

tag2 = newscopetag()

y = Ident(tag2, 1, :y)

# Reference

xdoty = Reference(x, y)

@test first(xdoty) == x
@test rest(xdoty) == Reference(y)
@test repr(xdoty) == "x.y"

xsub1 = Reference(x, nameless)

@test repr(xsub1) == "x[1]"

# retag, rename
@test gettag(first(retag(Dict(tag => tag2), xdoty))) == tag2
@test gettag(first(retag(Dict(tag2 => tag2), xdoty))) == tag
@test gettag(first(rest(retag(Dict(tag2 => tag), xdoty)))) == tag

@test repr(rename(tag, Dict(:x => :y, :y => :z), xdoty)) == "y.y"
@test repr(rename(tag2, Dict(:x => :y, :y => :z), xdoty)) == "x.z"

# Binding

bind_x = Binding{String}(:x, Set([:x, :X]), "ex")
bind_y = Binding{String}(:y, Set([:y, :Y]), "why")
@test nameof(bind_x) == :x
@test getvalue(bind_x) == "ex"
@test getaliases(bind_x) == Set([:x,:X])

# Scope

xy_scope = Scope([bind_x, bind_y])
tag = gettag(xy_scope)
x, y = idents(xy_scope, [:x, :Y])

@test xy_scope[x] == bind_x
@test xy_scope[y] == bind_y
@test_throws ScopeTagError xy_scope[Ident(tag2, 1, :y)]

end
