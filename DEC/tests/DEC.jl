module TestDEC

using DEC
using DEC: Roe, SortError, d, fresh!, ∂ₜ, ∧, Δ, ≐, ★
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

roe = Roe()

a = fresh!(roe, Scalar(), :a)
b = fresh!(roe, Scalar(), :b)

x = a + b
y = a + b

@test x == y
@test roe.graph[(a+b).id].data == Scalar()

ω = fresh!(roe, PrimalForm(1), :ω)
η = fresh!(roe, PrimalForm(0), :η)

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

(ssa, derivative_vars) = DEC.vfield(lotka_volterra)

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

function transitivity(pode)
    w = fresh!(pode, Scalar(), :w)
    ∂ₜ(w) ≐ 1 * w
    ∂ₜ(w) ≐ 2 * w
    w
end
_w = transitivity(roe)
# picks whichever expression it happens to visit first
EGraphs.extract!((∂ₜ(_w)), DEC.derivative_cost([DEC.extract!(_w)]))

## HEAT EQUATION

function heat_equation(pode)
    u = fresh!(pode, PrimalForm(0), :u)

    ∂ₜ(u) ≐ Δ(u)

    ([u], [])
end

using CombinatorialSpaces
using GeometryBasics
using OrdinaryDiffEq
Point2D = Point2{Float64}
Point3D = Point3{Float64}

rect = triangulated_grid(100, 100, 1, 1, Point3D)
d_rect = EmbeddedDeltaDualComplex2D{Bool, Float64, Point3D}(rect)
subdivide_duals!(d_rect, Circumcenter())

operator_lookup = DEC.precompute_matrices(d_rect, DiagonalHodge())

vf = DEC.vfield(heat_equation, operator_lookup)

U = first.(d_rect[:point])

constants_and_parameters = ()

tₑ = 500.0

@info("Precompiling Solver")
prob = ODEProblem(vf, U, (0, tₑ), constants_and_parameters)
soln = solve(prob, Tsit5())

function save_dynamics(save_file_name)
  time = Observable(0.0)
  h = @lift(soln($time))
  f = Figure()
  ax = CairoMakie.Axis(f[1,1], title = @lift("Heat at time $($time)"))
  gmsh = mesh!(ax, rect, color=h, colormap=:jet,
               colorrange=extrema(soln(tₑ)))
  #Colorbar(f[1,2], gmsh, limits=extrema(soln(tₑ).h))
  Colorbar(f[1,2], gmsh)
  timestamps = range(0, tₑ, step=5.0)
  record(f, save_file_name, timestamps; framerate = 15) do t
    time[] = t
  end
end

end