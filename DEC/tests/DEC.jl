module TestDEC

using DEC
using DEC: Decapode, SortError, d, fresh!, ∂ₜ, ∧, Δ, ≐
using Test
using Metatheory.EGraphs

@test Scalar() + Scalar() == Scalar()
@test Scalar() + PrimalForm(1) == PrimalForm(1)
@test PrimalForm(2) + Scalar() == PrimalForm(2)
@test_throws SortError PrimalForm(1) + PrimalForm(2)

# Scalar Multiplication
@test Scalar() * Scalar() == Scalar()
@test Scalar() * PrimalForm(1) == PrimalForm(1)
@test PrimalForm(2) * Scalar() == PrimalForm(2)
@test_throws SortError PrimalForm(2) * PrimalForm(1) 

# Exterior Product
@test PrimalForm(1) ∧ PrimalForm(1) == PrimalForm(2)

pode = Decapode()

a = fresh!(pode, Scalar(), :a)
b = fresh!(pode, Scalar(), :b)

x = a + b
y = a + b

@test x == y

ω = fresh!(pode, PrimalForm(1), :ω)
η = fresh!(pode, PrimalForm(0), :η)

@test ω ∧ η isa DEC.Var{PrimalForm(1)}
@test ω ∧ η == ω ∧ η

@test_throws SortError x ≐ ω 

ω ≐ (ω ∧ η)

∂ₜ(a) ≐ 3 * a + 5

EGraphs.extract!(∂ₜ(a), DEC.derivative_cost([DEC.extract!(a)]))

function lotka_volterra(pode)
    α = fresh!(pode, Scalar(), :α)
    β = fresh!(pode, Scalar(), :β)
    γ = fresh!(pode, Scalar(), :γ)

    w = fresh!(pode, Scalar(), :w)
    s = fresh!(pode, Scalar(), :s)

    ∂ₜ(s) ≐ α * s - β * w * s
    ∂ₜ(w) ≐ - γ * w - β * w * s

    ([w, s], [α, β, γ])
end

f = DEC.vfield(lotka_volterra)

function transitivity(pode)
    w = fresh!(pode, Scalar(), :w)
    ∂ₜ(w) ≐ 1 * w
    ∂ₜ(w) ≐ 2 * w
    w
end
_w = transitivity(pode)
# picks whichever expression it happens to visit first
EGraphs.extract!((∂ₜ(_w)), DEC.derivative_cost([DEC.extract!(_w)]))

function heat_equation(pode)
    u = fresh!(pode, PrimalForm(0), :u)

    ∂ₜ(u) ≐ Δ(u)

    ([u], [])
end

f = DEC.vfield(heat_equation)


end