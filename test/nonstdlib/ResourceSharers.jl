module TestResourceSharers

using Test

using GATlab.Util.Dtrys
using GATlab.Util.Dtrys: node, leaf
using GATlab.NonStdlib.ResourceSharers
using GATlab.NonStdlib.ResourceSharers: ocompose, oapply
using GATlab
using GATlab.Syntax.GATs: tcompose
using ComponentArrays

import Base: +, *, -

@theory ThRing begin
  default::TYPE
  zero::default
  one::default
  ((x::default) + (y::default))::default
  ((x::default) * (y::default))::default
  (-(x::default))::default
end

@rhizome ThRing rtop(a, b) begin
  X(a)
  Y(a, c.x = b)
end

@rhizome ThRing rX(a) begin
  A(x = a, y = a)
end

@rhizome ThRing rY(a, c.x) begin
  A(x = a, y = a)
  B(t = c.x)
end

@test sprint(show, rtop) isa String

r = ocompose(rtop, Dtry(■.X => rX, ■.Y => rY))

@resource_sharer ThRing Spring begin
  variables = x, v
  params = k
  update = (state, params) -> (x = state.v, v = -params.k * state.x)
end;

@resource_sharer ThRing Gravity begin
  variables = v
  params = g
  update = (state, params) -> (v = - params.g,)
end;

@rhizome ThRing SpringGravity(x, v) begin
  spring(x, v)
  gravity(v)
end

@test sprint((io, r) -> show(io, r; theory=ThRing.Meta.theory), Gravity) isa String

s = oapply(SpringGravity, Dtry(■.spring => Spring, ■.gravity => Gravity));

body = toexpr(GATContext(ThRing.Meta.theory, s.update.context), s.update.body)

zero() = 0.0

eval(
  :(update(state, params) = ComponentArray(;$(body.args...)))
)

update((x = 0.0, v = 1.0), (spring = (k = 1.0,), gravity = (g = 9.8,)))

init = ComponentArray(x = 0.0, v = 1.0)
params = ComponentArray(spring = (k = 1.0,), gravity = (g = 9.8,))

function euler(init, params, v, dt, steps)
  values = Vector{typeof(init)}(undef, steps+1)
  values[1] = init
  for i in 1:steps
    values[i+1] = values[i] .+ (dt .* v(values[i], params))
  end
  values
end

traj = euler(init, params, update, 0.1, 100);

end
