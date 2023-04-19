module ContextMapTests

using Test
using Gatlab

f = @context_map ThCategory [x::Ob, y::Ob, f::Hom(x,y)] [x::Ob, y::Ob, f::Hom(y,x)] begin
  x = y
  y = x
  f = f
end

@test length(f.dom) == 3
@test index(f.morphism[3].head) == 3

g = @context_map ThCategory [(a,b)::Ob, f::Hom(a,b)] [(c,d)::Ob, f::Hom(c,d)] begin
  a = c
  b = d
  f = f
end

@test length(g.dom) == 3
@test length(g.codom) == 3

const CM = ContextMaps.Impl

@test length(CM.mcompose(g.dom,g.dom)) == 6
@test length(CM.mcompose(g.dom,g.codom)) == 6
@test CM.mcompose(g.dom,g.dom).ctx[6][2].args == [Trm(Lvl(4; context=true)), Trm(Lvl(5; context=true))]

end
