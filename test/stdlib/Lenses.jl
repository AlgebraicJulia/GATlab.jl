module LensesTest

using Test
using Gatlab
using AlgebraicPetri


"""
    f#
R³ <--- R²
    f
R³ ---> R³
"""

sir = @lens ThElementary begin
  dom = [s, i, r] | [ds, di, dr]
  codom = [s, i, r] | [β, γ]
  expose = begin
    s = s
    i = i
    r = r
  end
  update = begin
    ds = -β * (s * i)
    di = β * (s * i) + (- γ) * i
    dr = γ * i
  end
end

sir_pn = LabelledPetriNet([:s, :i, :r], 
                          :β => ((:s, :i), (:i, :i)), :γ => (:i, :r))
sir2 = lens_dynamics(sir_pn) # equivalent up to ring axioms
@test sir2.dom == sir.dom && sir2.codom == sir.codom

const_params = @lens ThElementary begin
  dom = [s, i, r] | [β, γ]
  codom = [] | []
  expose = begin
  end
  update = begin
    β = one
    γ = one + one
  end
end

composed = compose(sir, const_params)

@test length(composed.codom.pos) == 0
@test length(composed.morphism.expose) == 0
@test length(composed.morphism.update) == 3

lotka_voltera = @lens ThElementary begin
  dom = [wolf, sheep] | [dwolf, dsheep]
  codom = [wolf, sheep] | [graze, predation, death]
  expose = begin
    wolf = wolf
    sheep = sheep
  end
  update = begin
    dwolf = -(death * wolf) + predation * (wolf * sheep)
    dsheep = - predation * (wolf * sheep) + graze * sheep
  end
end

sir_lv = mcompose(sir, lotka_voltera)

@test length(sir_lv.dom.pos) == 5
@test length(sir_lv.codom.dir) == 5

const_paramsₕ = @lens ThElementary begin
  dom = [s, i, r] | [β, γ]
  codom = [h] | []
  expose = begin
    h = i * (one + one + one)
  end
  update = begin
    β = one
    γ = one + one
  end
end

composedₕ = compose(sir, const_paramsₕ)

@test length(composedₕ.codom.pos) == 1
@test length(composedₕ.morphism.expose) == 1
@test length(composedₕ.morphism.update) == 3

# # Periodic Beta System

periodic_params = @lens ThElementary begin
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

sir_and_periodic = mcompose(sir, periodic_params)

wiring = @lens ThElementary begin
  dom = [s, i, r, β, γ] | [β, γ, β₀, kᵦ, γ₀, kᵧ]
  codom = [s, i, r] | [β₀, kᵦ, γ₀, kᵧ]
  expose = begin
    s = s
    i = i
    r = r
  end
  update = begin
    β = β
    γ = γ
    β₀ = β₀
    kᵦ = kᵦ
    γ₀ = γ₀
    kᵧ = kᵧ
  end
end

composed = compose(sir_and_periodic, wiring)

@test length(composed.codom.pos) == 3
@test length(composed.morphism.expose) == 3
@test length(composed.morphism.update) == 5

end
