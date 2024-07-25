module TestRoe

using Test
using Metatheory.EGraphs

# Test question: are function calls in our theory both idempotent and correctly typing expressions?

# Instantiate a new Roe with two variables of type Var{Scalar}
roe = Roe()
a = fresh!(roe, Scalar(), :a)
b = fresh!(roe, Scalar(), :b)

# Write the same expresison twice but with different variable bindings. We expect that each `+` dispatches its Var{S} method defined in Roe/RoeFunctions.jl, which adds a new call to the egraph.
x = a + b
y = a + b

# We expect that `+` is idempotent; addcall! checks if the + call is already present in the egraph with the two ids for `a` and `b`. 
@test x == y

# We also check that the type of (a+b) is a Scalar.
@test roe.graph[(a+b).id].data == Scalar()

# Test question: 

# Now we define two primal forms.
ω = fresh!(roe, PrimalForm(1), :ω)
η = fresh!(roe, PrimalForm(0), :η)

# Is the wedge product of a 0-form and 1-form a 1-form?
@test ω ∧ η isa DEC.Var{PrimalForm(1)}

# Is the addcall! function idempotent?
@test ω ∧ η == ω ∧ η

@test_throws SortError x ≐ ω 

# Assert that ω is the same as the expression ω∧η
ω ≐ (ω ∧ η)

# Test question: can we extract a term from the e-graph?

# Assert to the egraph that ∂ₜ(a) is 3*a + 5
∂ₜ(a) ≐ 3 * a + 5

EGraphs.extract!(∂ₜ(a), DEC.derivative_cost([DEC.extract!(a)]))

# Test question: given a model with a partial derivative defined by two expressions with the same astsize, which expression is extracted? 

function transitivity(roe)
    w = fresh!(roe, Scalar(), :w)
    ∂ₜ(w) ≐ 1 * w
    ∂ₜ(w) ≐ 2 * w
    w
end
_w = transitivity(roe)
# picks whichever expression it happens to visit first
EGraphs.extract!((∂ₜ(_w)), DEC.derivative_cost([DEC.extract!(_w)]))


end
