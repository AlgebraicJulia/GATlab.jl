module ContextMapTests

using Test
using Gatlab

f = @context_map ThCategory [x::Ob, y::Ob, f::Hom(x,y)] [x::Ob, y::Ob, f::Hom(y,x)] begin
  x = y
  y = x
  f = f
end

@test length(f.dom) == 3
@test index(f.values[3].head) == 3

g = @context_map ThCategory [(a,b)::Ob, f::Hom(a,b)] [(c,d)::Ob, f::Hom(c,d)] begin
  a = c
  b = d
  f = f
end

@test length(g.dom) == 3
@test length(g.codom) == 3

@test length(coproduct(g.dom,g.dom)) == 6
@test length(coproduct(g.dom,g.codom)) == 6
@test g.dom.ctx[1][2].head == Lvl(1) # a is an object?
@test coproduct(g.dom,g.dom).ctx[1][2].head == Lvl(1) # a is an object?
@test coproduct(g.dom,g.dom).ctx[2][2].head == Lvl(1) # b is an object?
@test coproduct(g.dom,g.dom).ctx[3][2].head == Lvl(2) # f is a hom?
@test coproduct(g.dom,g.dom).ctx[4][2].head == Lvl(1) # a is an object?
@test coproduct(g.dom,g.dom).ctx[5][2].head == Lvl(1) # b is an object?
@test coproduct(g.dom,g.dom).ctx[6][2].head == Lvl(2) # f is a hom?
@test coproduct(g.dom,g.dom).ctx[6][2].args == [Trm(Lvl(4; context=true)), Trm(Lvl(5; context=true))]

end
