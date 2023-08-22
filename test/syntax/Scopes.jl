module TestScopes

using Test, Gatlab

# Ident 

tag = newscopetag()

x = Ident(tag, 1, :x)

@test tagof(x) == tag
@test levelof(x) == 1
@test nameof(x) == :x
@test repr(x) == "x"

nameless = Ident(tag, 1, nothing)

@test repr(nameless) == "#1"

tag2 = newscopetag()


y = Ident(tag2, 1, :y)

# Path 

xdoty = Path(x, Path(y))

@test firstof(xdoty) == x
@test restof(xdoty) == Path(y)
@test repr(xdoty) == "x.y"

xsub1 = Path(x, Path(nameless))

@test repr(xsub1) == "x[1]"

# retag, rename
@test tagof(firstof(retag(Dict(tag=>tag2), xdoty))) == tag2
@test tagof(firstof(retag(Dict(tag2=>tag2), xdoty))) == tag
@test tagof(firstof(restof(retag(Dict(tag2=>tag), xdoty)))) == tag

@test repr(rename(tag, Dict(:x=>:y, :y=>:z), xdoty)) == "y.y"
@test repr(rename(tag2, Dict(:x=>:y, :y=>:z), xdoty)) == "x.z"

# NamedElt

ne_x = NamedElt{String}(:x, Set([:x, :X]), "ex")
ne_y = NamedElt{String}(:y, Set([:y, :Y]), "why")
@test nameof(ne_x) == :x
@test valueof(ne_x) == "ex"
@test aliasesof(ne_x) == Set([:x,:X])

xy_scope = Scope([ne_x, ne_y])
tag = tagof(xy_scope)
x, y = Ident.(tag, 1:2, [:x,:Y])
@test namesof(xy_scope)[:x][nothing] == 1
@test namesof(xy_scope)[:Y][nothing] == 2

@test xy_scope[x] == "ex"
@test xy_scope[y] == "why"
@test_throws ScopeTagMismatch xy_scope[Ident(tag2, 1, :y)]

end
