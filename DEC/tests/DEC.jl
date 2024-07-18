module TestDEC

using DEC
using DEC: Decapode, SortError, d, fresh!, ∂ₜ, ∧, ≐
using Test
using Metatheory.EGraphs

@test Scalar() + Scalar() == Scalar()
@test Scalar() + Form(1) == Form(1)
@test Form(2) + Scalar() == Form(2)
@test_throws SortError Form(1) + Form(2)

# Scalar Multiplication
@test Scalar() * Scalar() == Scalar()
@test Scalar() * Form(1) == Form(1)
@test Form(2) * Scalar() == Form(2)
@test_throws SortError Form(2) * Form(1) 

# Exterior Product
@test Form(1) ∧ Form(1) == Form(2)

pode = Decapode()

a = fresh!(pode, Scalar(), :a)
b = fresh!(pode, Scalar(), :b)

x = a + b
y = a + b

@test x == y

ω = fresh!(pode, Form(1), :ω)
η = fresh!(pode, Form(0), :η)

@test ω ∧ η isa DEC.Var{Form(1)}
@test ω ∧ η == ω ∧ η

@test_throws SortError x ≐ ω 

ω ≐ (ω ∧ η)

∂ₜ(a) ≐ 3 * a + 5

EGraphs.extract!(pode.graph, DEC.noderivcost, (∂ₜ(a)).id)

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

EGraphs.extract!(pode.graph, DEC.noderivcost, (∂ₜ(w)).id)

function transitivity(pode)
    w = fresh!(pode, Scalar(), :w)
    ∂ₜ(w) ≐ 1 * w
    ∂ₜ(w) ≐ 2 * w
    w
end
_w = transitivity(pode)
# picks whichever expression it happens to visit first
EGraphs.extract!(pode.graph, DEC.noderivcost, (∂ₜ(_w)).id)

EGraphs.extract!(pode.graph, EGraphs.astsize, w.id)

end