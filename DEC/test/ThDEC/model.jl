using DEC
import DEC: Δ, ∧

# load other dependencies
using ComponentArrays
using CombinatorialSpaces 
using GeometryBasics
using OrdinaryDiffEq
Point2D = Point2{Float64}
Point3D = Point3{Float64}

# plotting
using CairoMakie

## 1-D HEAT EQUATION

# initialize the model
function heat_equation(roe)
  u = fresh!(roe, PrimalForm(0), :u)

  ∂ₜ(u) ≐ Δ(u)

  ([u], [])
end

# initialize primal and dual meshes.
rect = triangulated_grid(100, 100, 1, 1, Point3D);
d_rect = EmbeddedDeltaDualComplex2D{Bool, Float64, Point3D}(rect);
subdivide_duals!(d_rect, Circumcenter());

# precompute matrices from operators in the DEC theory.
op_lookup = ThDEC.create_dynamic_model(d_rect, DiagonalHodge())

# produce a vector field.
vf = vfield(heat_equation, op_lookup)

U = first.(d_rect[:point]);
constants_and_parameters = ()
t0 = 50.0

@info("Precompiling Solver")
prob = ODEProblem(vf, U, (0, t0), constants_and_parameters);
soln = solve(prob, Tsit5());

save_dynamics(soln, t0, "heat-1D.gif")

## 1-D HEAT EQUATION WITH DIFFUSIVITY

function new_heat_equation(roe)
  u = fresh!(roe, PrimalForm(0), :u)
  k = fresh!(roe, Scalar(), :k)
  ℓ = fresh!(roe, Scalar(), :ℓ)

  ∂ₜ(u) ≐ ℓ * k * Δ(u)
  
  ([u], [k, ℓ])
end

# we can reuse the mesh and operator lookup
vf = vfield(new_heat_equation, op_lookup)

# we can reuse the initial condition U. However we need to specify the diffusivity constant 
constants_and_parameters = ComponentArray(k=0.25,ℓ=2,);

# this is a shim
DEC.k = :k; DEC.ℓ = :ℓ;

# Let's set the time 
t0 = 500

@info("Precompiling solver")
prob = ODEProblem(vf, U, (0, t0), constants_and_parameters);

soln = solve(prob, Tsit5());

save_dynamics(soln, t0, "heat-1D-scalar.gif")
