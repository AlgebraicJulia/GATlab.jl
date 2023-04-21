module TestSerialization

using Test
using Gatlab
import JSON

periodic_params = @lens ThRing begin
  dom = [β, γ] | [dβ, dγ]
  codom = [β, γ] | [β₀, kᵦ, γ₀, kᵧ]
  expose = begin
    β = β
    γ = γ
  end
  update = begin
    dβ = -kᵦ*(β + (-β₀))
    dγ = -kᵧ*(γ + (-γ₀))
  end
end

rehydrated = parse_json(JSON.parse(JSON.json(periodic_params)), SimpleKleisliLens{ThRing})

@test rehydrated.dom == periodic_params.dom
@test rehydrated.codom == periodic_params.codom
@test rehydrated.morphism == periodic_params.morphism
@test rehydrated == periodic_params

end
