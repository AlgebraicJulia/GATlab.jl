module TestSerialization

using Test
using Gatlab
import JSON

periodic_params = @lens ThRing begin
  dom = [β, γ] | [:d(β), :d(γ)]
  codom = [β, γ] | [β₀, kᵦ, γ₀, kᵧ]
  expose = begin
    β = β
    γ = γ
  end
  update = begin
    :d(β) = -kᵦ*(β + (-β₀))
    :d(γ) = -kᵧ*(γ + (-γ₀))
  end
end

rehydrated = parse_json(JSON.parse(JSON.json(periodic_params)), SimpleKleisliLens{ThRing.T})

@test rehydrated.dom == periodic_params.dom
@test rehydrated.codom == periodic_params.codom
@test rehydrated.morphism == periodic_params.morphism
@test rehydrated == periodic_params

end
