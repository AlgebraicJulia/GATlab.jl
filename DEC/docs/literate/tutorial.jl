# This tutorial is a slower-paced introduction into the design. Here, we will construct a simple exponential model.
using DEC
using Test
using Metatheory.EGraphs
using ComponentArrays
using GeometryBasics
using OrdinaryDiffEq
Point2D = Point2{Float64}
Point3D = Point3{Float64}

using CairoMakie

# We define our model of exponential growth. This model is a function which accepts a Roe and returns a tuple of State and Parameter variables. Let's break it down:
#
# 1. Function adds root variables (::RootVar) to the Roe. The root variables have no child nodes.
# 2. Our model makes claims about what terms equal one another. The "≐" operator is an infix of "equate!" which claims unites the ids of the left and right VecExprs.
# 3. The State and Parameter variables are returned. Each variable points to the same parent Roe.
#
#
# Each variable points to the same Roe. 
function exp_growth(roe)
  u = fresh!(roe, PrimalForm(0), :u)
  k = fresh!(roe, Scalar(), :k)

  ∂ₜ(u) ≐ k * u

  ([u], [k])
end

# We now need to initialize the primal and dual meshes we'll need to compute with.
rect = triangulated_grid(100, 100, 1, 1, Point3D);
d_rect = EmbeddedDeltaDualComplex2D{Bool, Float64, Point3D}(rect);
subdivide_duals!(d_rect, Circumcenter());

# For the theory of the DEC, we will need to associate each operator to the precomputed matrix specific to our dual mesh.
operator_lookup = ThDEC.create_dynamic_model(d_rect, DiagonalHodge())

# We now need to convert our model to an ODEProblem. In our case, ``vfield`` produces 
vf = vfield(exp_growth, operator_lookup)

U = first.(d_rect[:point]);

constants_and_parameters = ComponentArray(k=-0.5,)

t0 = 50.0

@info("Precompiling Solver")
prob = ODEProblem(vf, U, (0, t0), constants_and_parameters);
soln = solve(prob, Tsit5());

save_dynamics(soln, "decay.gif")

