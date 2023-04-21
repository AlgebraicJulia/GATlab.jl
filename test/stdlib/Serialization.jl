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

@test parse_json(JSON.parse(JSON.json(periodic_params)), SimpleKleisliLens{ThRing}) == periodic_params

end
