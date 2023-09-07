module TestScopeTrees

using Test, Gatlab

t = wrap(
  :a => pure(1),
  :b => wrap(:x => pure(2), :y => pure(1)),
  :c => wrap(:f => wrap(:g => pure(4)))
)

r = fromexpr(t, :(c.f.g), Reference)

@test toexpr(t, r) == :(c.f.g)

@test isnode(t)
@test isleaf(getvalue(t, :a))
@test nameof.(first.(keys(t))) == [:a, :b, :b, :c]
@test keys(t)[3] == fromexpr(t, :(b.y), Reference)
@test haskey(t, r)
@test t[r] == 4
@test_throws KeyError t[fromexpr(t, :(c.f), Reference)]
@test_throws KeyError t[fromexpr(t, :(_), Reference)]

using .ThCategory

t1 = wrap(:a => pure(1), :b => pure(1), :c => pure(2))
t2 = wrap(:x => wrap(:p => pure(3), :q => pure(2)), :y => pure(7))
a, b, c = fromexpr.(Ref(t1), [:a, :b, :c], Ref(Reference))
xp, xq, y = fromexpr.(Ref(t2), [:(x.p), :(x.q), :y], Ref(Reference))
f = ScopeTreeHom(a => (y, [6]), b => (xp, [2]), c => (xq, [2,2]))

keys(f.map) ⊆ keys(t1)
keys(f.map) ⊇ keys(t1)

@withmodel ScopeTreeC{Int, Vector{Int}, FinSetC}(FinSetC()) (Ob, Hom, compose, id) begin
  @test Ob(t)
  @test Hom(f, t1, t2)
end


end
