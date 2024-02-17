module TestResourceSharers

using GATlab.Syntax.Tries
using GATlab.Syntax.Tries: node, leaf
using GATlab.NonStdlib.ResourceSharers
using GATlab.NonStdlib.ResourceSharers: ocompose, oapply
using GATlab
using GATlab.Syntax.GATs: tcompose

@rhizome ThMonoid rtop(a, b) begin
  X(a)
  Y(a, c.x = b)
end

@rhizome ThMonoid rX(a) begin
  A(x = a, y = a)
end

@rhizome ThMonoid rY(a, c.x) begin
  A(x = a, y = a)
  B(t = c.x)
end

r = ocompose(rtop, node(:X => leaf(rX), :Y => leaf(rY)))

@theory ThRing begin
  default::TYPE
  zero::default
  one::default
  ((x::default) + (y::default))::default
  ((x::default) * (y::default))::default
  (-(x::default))::default
end

deftype = fromexpr(ThRing.Meta.theory, :default, AlgType)
spring_variables = node(:x => leaf(Variable(true, deftype)), :v => leaf(Variable(true, deftype)))
spring_params = tcompose(node(:k => leaf(deftype)))
@algebraic ThRing spring_update(s::(x,v), p::(k,)) = (x = s.v, v = - p.k * s.x)

Spring = ResourceSharer(spring_variables, spring_params, first(values(spring_update.methods)))

gravity_variables = node(:v => leaf(Variable(true, deftype)))
gravity_params = tcompose(node(:g => leaf(deftype)))
@algebraic ThRing gravity_update(s::(v,), p::(g,)) = (v = - p.g,)

Gravity = ResourceSharer(gravity_variables, gravity_params, first(values(gravity_update.methods)))

@rhizome ThRing SpringGravity(x, v) begin
  spring(x, v)
  gravity(v)
end

z = fromexpr(ThRing.Meta.theory, :(zero()), AlgTerm)
p = fromexpr(ThRing.Meta.theory, :(zero() + zero()), AlgTerm)

oapply( SpringGravity, node(:spring => leaf(Spring), :gravity => leaf(Gravity)), (p.body.head, p.body.method), (z.body.head, z.body.method))

end
