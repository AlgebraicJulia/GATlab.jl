module LensesTest

using Test
using Gatlab


"""
    f#
R³ <--- R²
    f
R³ ---> R³
"""

sir = @lens ThRing begin
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

const_params = @lens ThRing begin
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

lotka_voltera = @lens ThRing begin
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

const_paramsₕ = @lens ThRing begin
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

# expose₁ = @context_map ThRing [β, γ] [β,γ] begin
#    β = β
#    γ = γ
# end

# # β₀ = 0.5

# update₁ = @context_map ThRing [dβ, dγ] [β, γ, β₀] begin
#     dβ = -(β - β₀)
#     dγ = 0
# end

periodic_params = @lens ThRing begin
  dom = [β, γ] | [dβ, dγ]
  codom = [] | [β₀, kᵦ, γ₀, kᵧ]
  expose = begin

  end
  update = begin
    dβ = -kᵦ*(β - β₀)
    dγ = -kᵧ*(γ - γ₀)
  end
end

# This should error because 5 != 4
composed = compose(sir, periodic_params)


end
