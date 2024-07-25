# TODO under construction
module TestSSAExtract

# AlgebraicJulia dependencies
using DEC: AbstractSort
import DEC.ThDEC

# other dependencies
using Test
using LinearAlgebra
using Metatheory

# Test question: SSA

function lotka_volterra(roe)
    α = fresh!(roe, Scalar(), :α)
    β = fresh!(roe, Scalar(), :β)
    γ = fresh!(roe, Scalar(), :γ)

    w = fresh!(roe, Scalar(), :w)
    s = fresh!(roe, Scalar(), :s)

    ∂ₜ(s) ≐ α * s - β * w * s
    ∂ₜ(w) ≐ - γ * w - β * w * s

    ([w, s], [α, β, γ])
end

# a model ThRing => GL(ℝ) is necessary here
ops = Dict{TA, Any}(
  TA(-, AbstractSort[Scalar()]) => -I,
  TA(-, AbstractSort[Scalar(), Scalar()]) => I,
  TA(*, AbstractSort[Scalar(), Scalar()]) => I,) 

(ssa, derivative_vars) = vfield(lotka_volterra, ops)

basicprinted(x; color=false) = sprint(show, x; context=(:color=>color))

@test basicprinted(ssa) == """
SSA: 
  %1 = γ#2
  %2 = -(%1::Scalar(),)
  %3 = w#3
  %4 = *(%2::Scalar(), %3::Scalar())
  %5 = β#1
  %6 = *(%5::Scalar(), %3::Scalar())
  %7 = s#4
  %8 = *(%6::Scalar(), %7::Scalar())
  %9 = -(%4::Scalar(), %8::Scalar())
  %10 = α#0
  %11 = *(%10::Scalar(), %7::Scalar())
  %12 = -(%11::Scalar(), %8::Scalar())
"""

roe = Roe()

a = fresh!(roe, Scalar(), :a)
b = fresh!(roe, Scalar(), :b)

ssa = SSAExtract.SSA()

function term_select(g::EGraph, id::Id)
    g[id].nodes[1]
end

extract!(roe.graph, ssa, (a + b).id, term_select)

ssa

end
