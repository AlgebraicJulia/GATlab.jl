module LensesTest

using Test
using Gatlab


"""
    f#
R³ <--- R²
    f
R³ ---> R³
"""

expose = @context_map ThRing [s,i,r] [s,i,r] begin
    s = s
    i = i
    r = r
end

update = @context_map ThRing [ds, di, dr] [s, i, r, β, γ] begin
    ds = -(β * s * i)
    di = β * s * i - γ * i
    dr = γ * i
end

sir = SimpleKleisliLens{ThRing}(
    SimpleArena{ThRing}(
        (@context ThRing [s,i,r]),
        (@context ThRing [ds, di, dr])
    ),
    SimpleArena{ThRing}(
        (@context ThRing [s,i,r]),
        (@context ThRing [β, γ]),
    ),
    expose.values,
    update.values
)


expose′ = @context_map ThRing [] [s,i,r] begin
end

update′ = @context_map ThRing [β, γ] [s,i,r] begin
    β = one
    γ = one + one
end

const_params = SimpleKleisliLens{ThRing}(
    SimpleArena{ThRing}(
        (@context ThRing [s,i,r]),
        (@context ThRing [β, γ])
    ),
    SimpleArena{ThRing}(
        (@context ThRing []),
        (@context ThRing [])
    ),
    expose′.values,
    update′.values
)


compose(sir, const_params)
# Periodic Beta System

expose₁ = @context_map ThRing [β, γ] [β,γ] begin
   β = β
   γ = γ
end

# β₀ = 0.5

update₁ = @context_map ThRing [dβ, dγ] [β, γ, β₀] begin
    dβ = -(β - β₀)
    dγ = 0
end

end