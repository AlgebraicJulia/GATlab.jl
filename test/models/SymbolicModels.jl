module TestSymbolicModels

using GATlab, Test

abstract type CategoryExpr{T} <: GATExpr{T} end

abstract type ObExpr{T} <: CategoryExpr{T} end

abstract type HomExpr{T} <: CategoryExpr{T} end

@symbolic_model FreeCategory{ObExpr, HomExpr} ThCategory begin
  compose(f::Hom, g::Hom) = associate_unit(new(f,g), ThCategory.id)
end

x, y = FreeCategory.Ob{:generator}([:x], []), FreeCategory.Ob{:generator}([:y], [])
f = FreeCategory.Hom{:generator}([:f], [x, y])

@test x isa ObExpr{:generator}
@test ThCategory.id(x) isa HomExpr{:id}
@test ThCategory.compose(ThCategory.id(x), f) == f

# Monoid
########

""" Theory of monoids.
"""
@theory ThMonoid begin
  Elem::TYPE
  munit()::Elem
  mtimes(x::Elem,y::Elem)::Elem
end

""" Syntax for the theory of monoids.
"""
@symbolic_model FreeMonoid{GATExpr} ThMonoid

import .ThMonoid: Elem
using .ThMonoid

Elem(mod::Module, args...) = Elem(mod.Elem, args...)

@test isa(FreeMonoid, Module)
# @test occursin("theory of monoids", string(Docs.doc(FreeMonoid)))
# @test sort(names(FreeMonoid)) == sort([:FreeMonoid, :Elem])

x, y, z = Elem(FreeMonoid,:x), Elem(FreeMonoid,:y), Elem(FreeMonoid,:z)
@test nameof(x) == :x
@test isa(mtimes(x,y), FreeMonoid.Elem)
@test isa(munit(FreeMonoid.Elem), FreeMonoid.Elem)
@test gat_typeof(x) == :Elem
@test gat_typeof(mtimes(x,y)) == :Elem
@test mtimes(mtimes(x,y),z) != mtimes(x,mtimes(y,z))

# # Test equality
@test x == Elem(FreeMonoid,:x)
@test x != y
@test Elem(FreeMonoid,"X") == Elem(FreeMonoid,"X")
@test Elem(FreeMonoid,"X") != Elem(FreeMonoid,"Y")

# Test hash
@test hash(x) == hash(x)
@test hash(x) != hash(y)
@test hash(mtimes(x,y)) == hash(mtimes(x,y))
@test hash(mtimes(x,y)) != hash(mtimes(x,z))

@symbolic_model FreeMonoidAssoc{GATExpr} ThMonoid begin
  mtimes(x::Elem, y::Elem) = associate(new(x,y))
end

x, y, z = [ Elem(FreeMonoidAssoc,sym) for sym in [:x,:y,:z] ]
e = munit(FreeMonoidAssoc.Elem)
@test mtimes(mtimes(x,y),z) == mtimes(x,mtimes(y,z))
@test mtimes(e,x) != x && mtimes(x,e) != x

@symbolic_model FreeMonoidAssocUnit{GATExpr} ThMonoid begin
  mtimes(x::Elem, y::Elem) = associate_unit(new(x,y), munit)
end

x, y, z = [ Elem(FreeMonoidAssocUnit,sym) for sym in [:x,:y,:z] ]
e = munit(FreeMonoidAssocUnit.Elem)
@test mtimes(mtimes(x,y),z) == mtimes(x,mtimes(y,z))
@test mtimes(e,x) == x && mtimes(x,e) == x

abstract type MonoidExpr{T} <: GATExpr{T} end
@symbolic_model FreeMonoidTyped{MonoidExpr} ThMonoid

x = Elem(FreeMonoidTyped.Elem, :x)
@test FreeMonoidTyped.Elem <: MonoidExpr
@test isa(x, FreeMonoidTyped.Elem) && isa(x, MonoidExpr)

# @signature ThMonoidNumeric{Elem} <: ThMonoid{Elem} begin
#   elem_int(x::Int)::Elem
# end

# @syntax FreeMonoidNumeric ThMonoidNumeric

# x = elem_int(FreeMonoidNumeric.Elem, 1)
# @test isa(x, FreeMonoidNumeric.Elem)
# @test first(x) == 1

""" A monoid with two distinguished elements.
"""
@theory ThMonoidTwo <: ThMonoid begin
  one()::Elem
  two()::Elem
end

""" The free monoid on two generators.
"""
# @symbolic_model FreeMonoidTwo{GATExpr} ThMonoidTwo begin
#   Elem(::Type{Elem}, value) = error("No extra generators allowed!")
# end

# x, y = one(FreeMonoidTwo.Elem), two(FreeMonoidTwo.Elem)
# @test all(isa(expr, FreeMonoidTwo.Elem) for expr in [x, y, mtimes(x,y)])
# @test_throws ErrorException Elem(FreeMonoidTwo, :x)

# Category
##########

module CatTests

using GATlab, Test

@theory ThCategory begin
  Ob::TYPE
  Hom(dom::Ob, codom::Ob)::TYPE

  id(X::Ob)::Hom(X,X)
  compose(f::Hom(X,Y), g::Hom(Y,Z))::Hom(X,Z) ⊣ [X::Ob, Y::Ob, Z::Ob]
end

@symbolic_model FreeCategory{GATExpr, GATExpr} ThCategory begin
  compose(f::Hom, g::Hom) = associate(new(f,g))
end

@test isa(FreeCategory, Module)
@test sort(names(FreeCategory)) == sort([:FreeCategory, :Ob, :Hom])

using .ThCategory

X, Y, Z, W = [ Ob(FreeCategory.Ob, sym) for sym in [:X, :Y, :Z, :W] ]
f, g, h = Hom(:f, X, Y), Hom(:g, Y, Z), Hom(:h, Z, W)
@test isa(X, FreeCategory.Ob) && isa(f, FreeCategory.Hom)
@test_throws MethodError FreeCategory.Hom(:f)
@test dom(f) == X
@test codom(f) == Y

@test isa(id(X), FreeCategory.Hom)
@test dom(id(X)) == X
@test codom(id(X)) == X

@test isa(compose(f,g), FreeCategory.Hom)
@test dom(compose(f,g)) == X
@test codom(compose(f,g)) == Z
@test isa(compose(f,f), FreeCategory.Hom) # Doesn't check domains.
@test compose(compose(f,g),h) == compose(f,compose(g,h))

@symbolic_model FreeCategoryStrict{GATExpr, GATExpr} ThCategory begin
  compose(f::Hom, g::Hom) = associate(new(f,g; strict=true))
end

X, Y = Ob(FreeCategoryStrict.Ob, :X), Ob(FreeCategoryStrict.Ob, :Y)
f, g = Hom(:f, X, Y), Hom(:g, Y, X)

@test isa(compose(f,g), FreeCategoryStrict.Hom)
@test_throws SyntaxDomainError compose(f,f)

try
  compose(f,f)
catch e
  @test sprint(showerror, e) isa String
end

end

# Functor
#########

@instance ThMonoid{String} begin
  munit(::Type{String}) = ""
  mtimes(x::String, y::String) = string(x,y)
end

F(expr; kw...) = functor((String,), expr; kw...)

x, y, z = Elem(FreeMonoid,:x), Elem(FreeMonoid,:y), Elem(FreeMonoid,:z)
gens = Dict(x => "x", y => "y", z => "z")
@test F(mtimes(x,mtimes(y,z)); generators=gens) == "xyz"
@test F(mtimes(x,munit(FreeMonoid.Elem)); generators=gens) == "x"

terms = Dict(:Elem => (x) -> string(first(x)))
@test F(mtimes(x,mtimes(y,z)); terms=terms) == "xyz"
@test F(mtimes(x,munit(FreeMonoid.Elem)); terms=terms) == "x"

# Serialization
###############

using .ThCategory
ThCategory.Ob(m::Module, x) = Ob(m.Ob, x)

# To JSON
X, Y, Z = [ Ob(FreeCategory.Ob, sym) for sym in [:X, :Y, :Z] ]
f = Hom(:f, X, Y)
g = Hom(:g, Y, Z)
@test to_json_sexpr(X) == ["Ob", "X"]
@test to_json_sexpr(f) == ["Hom", "f", ["Ob", "X"], ["Ob", "Y"]]
@test to_json_sexpr(compose(f,g)) == [
  "compose",
  ["Hom", "f", ["Ob", "X"], ["Ob", "Y"]],
  ["Hom", "g", ["Ob", "Y"], ["Ob", "Z"]],
]
@test to_json_sexpr(f, by_reference=x->true) == "f"
@test to_json_sexpr(compose(f,g), by_reference=x->true) == ["compose","f","g"]
@test to_json_sexpr(true)

# From JSON
@test parse_json_sexpr(FreeMonoid, [:Elem, "x"]) == Elem(FreeMonoid, :x)
@test parse_json_sexpr(FreeMonoid, [:munit]) == munit(FreeMonoid.Elem)
@test parse_json_sexpr(FreeCategory, ["Ob", "X"]) == X
@test parse_json_sexpr(FreeCategory, ["Ob", "X"]; symbols=false) ==
  Ob(FreeCategory.Ob, "X")
@test parse_json_sexpr(FreeCategory, ["Hom", "f", ["Ob", "X"], ["Ob", "Y"]]) == f
@test parse_json_sexpr(FreeCategory, ["Hom", "f", ["Ob", "X"], ["Ob", "Y"]]; symbols=false) ==
  Hom("f", Ob(FreeCategory.Ob, "X"), Ob(FreeCategory.Ob, "Y"))
@test parse_json_sexpr(FreeCategory, ["Ob", true]) == Ob(FreeCategory, true)
@test_throws ErrorException parse_json_sexpr(FreeCategory, "X")

# Round trip
@test parse_json_sexpr(FreeCategory, to_json_sexpr(compose(f,g))) == compose(f,g)
@test parse_json_sexpr(FreeCategory, to_json_sexpr(id(X))) == id(X)

# Pretty Printing
#################

sexpr(expr::GATExpr) = sprint(show_sexpr, expr)
unicode(expr::GATExpr; all::Bool=false) =
  all ? sprint(show, MIME("text/plain"), expr) : sprint(show_unicode, expr)
latex(expr::GATExpr; all::Bool=false) =
  all ? sprint(show, MIME("text/latex"), expr) : sprint(show_latex, expr)

# Monoids

x, y, z = Elem.(Ref(FreeMonoid), [:x, :y, :z])

@test sexpr(mtimes(x,y)) == "(mtimes :x :y)"
@test unicode(mtimes(x,y)) == "mtimes{x,y}"
@test latex(mtimes(x, y)) == raw"\mathop{\mathrm{mtimes}}\left[x,y\right]"

# Categories


A, B = Ob(FreeCategory, :A), Ob(FreeCategory, :B)
f, g = Hom(:f, A, B), Hom(:g, B, A)

ThCategory.compose(f, g, h...) = compose(f, compose(g, h...))

import .SymbolicModels: show_unicode, show_latex

show_unicode(io::IO, expr::CategoryExpr{:compose}; kw...) =
  show_unicode_infix(io, expr, "⋅"; kw...)

show_latex(io::IO, expr::CategoryExpr{:id}; kw...) =
  show_latex_script(io, expr, "\\mathrm{id}")
show_latex(io::IO, expr::CategoryExpr{:compose}; paren::Bool=false, kw...) =
  show_latex_infix(io, expr, "\\cdot"; paren=paren)

function Base.show(io::IO, ::MIME"text/plain", expr::HomExpr)
  show_unicode(io, expr)
  print(io, ": ")
  show_unicode(io, dom(expr))
  print(io, " → ")
  show_unicode(io, codom(expr))
end

function Base.show(io::IO, ::MIME"text/latex", expr::HomExpr)
  print(io, "\$")
  show_latex(io, expr)
  print(io, " : ")
  show_latex(io, dom(expr))
  print(io, " \\to ")
  show_latex(io, codom(expr))
  print(io, "\$")
end

# String format
@test string(A) == "A"
@test string(f) == "f"
@test string(compose(f,g)) == "compose(f,g)"
@test string(compose(f,g,f)) == "compose(f,g,f)"
@test string(Ob(FreeCategory, nothing)) != ""

# S-expressions
@test sexpr(A) == ":A"
@test sexpr(f) == ":f"
@test sexpr(compose(f,g)) == "(compose :f :g)"
@test sexpr(compose(f,g,f)) == "(compose :f :g :f)"

# Infix notation (Unicode)
@test unicode(A) == "A"
@test unicode(A, all=true) == "A"
@test unicode(f) == "f"
@test unicode(f, all=true) == "f: A → B"
@test unicode(id(A)) == "id{A}"
@test unicode(compose(f,g)) == "f⋅g"

# Infix notation (LaTeX)
@test latex(A) == "A"
@test latex(A, all=true) == raw"$A$"
@test latex(f) == "f"
@test latex(f, all=true) == raw"$f : A \to B$"
@test latex(id(A)) == "\\mathrm{id}_{A}"
@test latex(compose(f,g)) == "f \\cdot g"

@test latex(Ob(FreeCategory, "x")) == "x"
@test latex(Ob(FreeCategory, "sin")) == "\\mathrm{sin}"
@test latex(Ob(FreeCategory, "\\alpha")) == "\\alpha"

@test sprint(show_latex_postfix, id(A), "i") == "{A}i"

# Groupoid

""" Theory of *groupoids*.
"""
@theory ThGroupoid <: ThCategory begin
  invert(f::(A → B))::(B → A) ⊣ [A::Ob, B::Ob]

  (f ⋅ invert(f) == id(A)) :: Hom(A, A) ⊣ [A::Ob, B::Ob, f::(A → B)]
  (invert(f) ⋅ f == id(B)) :: Hom(B, B) ⊣ [A::Ob, B::Ob, f::(A → B)]
end

using .ThGroupoid

@symbolic_model FreeGroupoid{ObExpr,HomExpr} ThGroupoid begin
  compose(f::Hom, g::Hom) = associate_unit_inv(new(f,g; strict=true), id, invert)
  invert(f::Hom) = distribute_unary(involute(new(f)), invert, compose,
                                 unit=id, contravariant=true)
end

A, B, C = Ob(FreeGroupoid, :A), Ob(FreeGroupoid, :B), Ob(FreeGroupoid, :C)
f, g, h, k = Hom(:f, A, B), Hom(:g, B, C), Hom(:h, B, A), Hom(:k, C, B)

# Domains and codomains
@test dom(invert(f)) == B
@test codom(invert(f)) == A

# Associativity and unitality
@test compose(compose(f,g),k) == compose(f,compose(g,k))
@test compose(id(A), f) == f
@test compose(f, id(B)) == f

# Inverse laws
@test compose(f,invert(f)) == id(A)
@test compose(invert(f),f) == id(B)
@test compose(invert(f),compose(f,g)) == g
@test compose(h,compose(invert(h),g)) == g
@test compose(compose(f,g),invert(g)) == f
@test compose(compose(k,invert(f)),f) == k
@test compose(compose(f,invert(k)),compose(k,invert(f))) == id(A)

# Inverses and composition
@test invert(compose(f,g)) == compose(invert(g),invert(f))
@test invert(id(A)) == id(A)

# Involution
@test invert(invert(f)) == f

# PointedSetCategory

"""
Theory of a pointed set-enriched category.
We axiomatize a category equipped with zero morphisms.

A functor from an ordinary category into a freely generated
pointed-set enriched category,
equivalently, a pointed-set enriched category in which no two nonzero maps
compose to a zero map, is a good notion
of a functor that's total on objects and partial on morphisms.
"""
@theory ThPointedSetCategory <: ThCategory begin
  zeromap(A::Ob,B::Ob)::Hom(A,B)
  (compose(zeromap(A,B),f::(B→C))==zeromap(A,C)) :: Hom(A, C) ⊣ [A::Ob,B::Ob,C::Ob]
  (compose(g::(A→B),zeromap(A,B))==zeromap(A,C)) :: Hom(A, C) ⊣ [A::Ob,B::Ob,C::Ob]
end

@symbolic_model FreePointedSetCategory{ObExpr,HomExpr} ThPointedSetCategory begin
  compose(f::Hom,g::Hom) = associate_unit(normalize_zero(new(f,g; strict=true)), id)
end

using .ThPointedSetCategory

A,B,C,D = map(x->Ob(FreePointedSetCategory,x),[:A,:B,:C,:D])
f,g,h = Hom(:f,A,B),Hom(:g,B,C),Hom(:h,C,D)
zAB,zBC,zAC = zeromap(A,B),zeromap(B,C),zeromap(A,C)
@test zAC == compose(f,zBC) == compose(zAB,g)
@test compose(f,zBC,h) == zeromap(A,D)

end
