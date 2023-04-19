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
    ds = -(β * s * i)
    di = β * s * i - γ * i
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

end
