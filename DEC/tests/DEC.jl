module TestDEC

# AlgebraicJulia dependencies
using DEC
import DEC.ThDEC: Δ

# other dependencies
using Test
using Metatheory.EGraphs
using CombinatorialSpaces 
using GeometryBasics
using OrdinaryDiffEq
Point2D = Point2{Float64}
Point3D = Point3{Float64}

# plotting
using CairoMakie

## 1-D HEAT EQUATION

function heat_equation(pode)
    u = fresh!(pode, PrimalForm(0), :u)

    ∂ₜ(u) ≐ Δ(u)

    ([u], [])
end

# initialize primal and dual meshes.
rect = triangulated_grid(100, 100, 1, 1, Point3D);
d_rect = EmbeddedDeltaDualComplex2D{Bool, Float64, Point3D}(rect);
subdivide_duals!(d_rect, Circumcenter());

# precompule matrices from operators in the DEC theory.
operator_lookup = ThDEC.precompute_matrices(d_rect, DiagonalHodge())

# produce a vector field
vf = vfield(heat_equation, operator_lookup)

#
U = first.(d_rect[:point]);

# TODO component arrays
constants_and_parameters = ()

tₑ = 500.0

@info("Precompiling Solver")
prob = ODEProblem(vf, U, (0, tₑ), constants_and_parameters);
soln = solve(prob, Tsit5());

function save_dynamics(save_file_name)
  time = Observable(0.0)
  h = @lift(soln($time))
  f = Figure()
  ax = CairoMakie.Axis(f[1,1], title = @lift("Heat at time $($time)"))
  gmsh = mesh!(ax, rect, color=h, colormap=:jet,
               colorrange=extrema(soln(tₑ)))
  Colorbar(f[1,2], gmsh)
  timestamps = range(0, tₑ, step=5.0)
  record(f, save_file_name, timestamps; framerate = 15) do t
    time[] = t
  end
end

end
