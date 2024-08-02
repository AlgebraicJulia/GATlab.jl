# Load AlgebraicJulia dependencies
using DEC
import DEC.ThDEC: Δ # conflicts with CombinatorialSpaces

# load other dependencies
using ComponentArrays
using CombinatorialSpaces 
using GeometryBasics
using OrdinaryDiffEq
Point2D = Point2{Float64}
Point3D = Point3{Float64}
using CairoMakie

## Here we define the 1D heat equation model with one state variable and no parameters. That is, given an e-graph "roe," we define `u` to be a primal 0-form. The root variable carries a reference to the e-graph which it resides in. We then assert that the time derivative of the state is just its Laplacian. We return the state variable. 
function heat_equation(roe)
    u = fresh!(roe, PrimalForm(0), :u)

    ∂ₜ(u) ≐ Δ(u)

    ([u], [])
end

# Since this is a model in the DEC, we need to initialize the primal and dual meshes.
rect = triangulated_grid(100, 100, 1, 1, Point3D);
d_rect = EmbeddedDeltaDualComplex2D{Bool, Float64, Point3D}(rect);
subdivide_duals!(d_rect, Circumcenter());

# Now that we have a dual mesh, we can associate operators in our theory with precomputed matrices from Decapodes.jl.
op_lookup = ThDEC.precompute_matrices(d_rect, DiagonalHodge())

# Now we produce a "vector field" function which, given a model and operators in a theory, returns a function to be passed to the ODESolver. In stages, this function 
#
#   1) extracts the Root Variables (state or parameter term) and runs the extractor along the e-graph, 
#   2) extracts the derivative terms from the model into an SSA
#   3) yields a function accepting derivative terms, state terms, and parameter terms, whose body is both the lines, and derivatives. 
vf = vfield(heat_equation, op_lookup)

# Let's initialize the 
U = first.(d_rect[:point]);

# TODO component arrays
constants_and_parameters = ()

# We will run this for 500 timesteps.
t0 = 500.0

@info("Precompiling Solver")
prob = ODEProblem(vf, U, (0, t0), constants_and_parameters);
soln = solve(prob, Tsit5());

## 1-D HEAT EQUATION WITH DIFFUSIVITY

function heat_equation_with_constants(roe)
  u = fresh!(roe, PrimalForm(0), :u)
  k = fresh!(roe, Scalar(), :k)
  ℓ = fresh!(roe, Scalar(), :ℓ)

  ∂ₜ(u) ≐ k * Δ(u)
  
  ([u], [k])
end

# we can reuse the mesh and operator lookup
vf = vfield(heat_equation_with_constants, operator_lookup)

# we can reuse the initial condition U but are specifying diffusivity constants. 
constants_and_parameters = ComponentArray(k=0.25,);
t0 = 500

@info("Precompiling solver")
prob = ODEProblem(vf, U, (0, t0), constants_and_parameters);
soln = solve(prob, Tsit5());


