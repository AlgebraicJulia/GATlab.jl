module TestSystems

using Test

using Gatlab

sirv = @system ThElementary begin
  @state [s, i, r, v]
  @params [β, γ, VP]
  :d(s) = - β * (s * i) + (-v) * s
  :d(i) = β * (s * i) + (-γ * i)
  :d(r) = -γ * i
  :d(v) = VP * s
end

vax_production = @system ThElementary begin
  @state [C, VP, t]
  @params [C_max, α, τ, I]
  :d(C) = C_max * sigmoid(I * α)
  :d(VP) = τ * C + (-sin(t))
  :d(t) = one
end

@test sirv.dom.dir == @context ThElementary [:d(s), :d(i), :d(r), :d(v)]

update_codom = ContextMaps.Impl.mcompose(sirv.dom.pos, sirv.codom.dir)

@test sirv.morphism.update[4] == @term ThElementary update_codom (VP * s)

@test vax_production.morphism.expose == ContextMaps.Impl.id(vax_production.dom.pos)

end
