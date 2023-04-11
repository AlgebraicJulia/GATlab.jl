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

g = @context_map ThCategory [a,b::Ob, f::Hom(a,b)] [c,d::Ob, f::Hom(c,d)] begin
  a = c
  b = d
  f = f
end

@test length(g.dom) == 3
@test length(g.codom) == 3

end
