import Decapodes
using StructEquality


"""    create_dynamic_model(sd, hodge)::Dict{TypedApplication, Any}

Given a matrix and a hodge star (DiagonalHodge() or GeometricHodge()), this returns a lookup dictionary between operators (as TypedApplications) and their corresponding matrices.

"""
function create_dynamic_model(sd, hodge)::Dict{TypedApplication, Any}
  Dict{TypedApplication, Any}(
    TA(*, Sort[Scalar(), Scalar()]) => 1,
    TA(*, Sort[Scalar(), PrimalForm(0)]) => 1,
    # Regular Hodge Stars
    TA(★, Sort[PrimalForm(0)]) => Decapodes.dec_mat_hodge(0, sd, hodge),
    TA(★, Sort[PrimalForm(1)]) => Decapodes.dec_mat_hodge(1, sd, hodge),
    TA(★, Sort[PrimalForm(2)]) => Decapodes.dec_mat_hodge(2, sd, hodge),

    # Inverse Hodge Stars
    TA(★, Sort[DualForm(0)]) => Decapodes.dec_mat_inverse_hodge(0, sd, hodge), 
    # TODO verify ^ why is this 1???
    TA(★, Sort[DualForm(1)]) => Decapodes.dec_pair_inv_hodge(Val{1}, sd, hodge), 
    # Special since Geo is a solver
    TA(★, Sort[DualForm(2)]) => Decapodes.dec_mat_inverse_hodge(0, sd, hodge),

    # Differentials
    TA(d, Sort[PrimalForm(0)]) => Decapodes.dec_mat_differential(0, sd),
    TA(d, Sort[PrimalForm(1)]) => Decapodes.dec_mat_differential(1, sd),

    # Dual Differentials
    TA(d, Sort[DualForm(0)]) => Decapodes.dec_mat_dual_differential(0, sd),
    TA(d, Sort[DualForm(1)]) => Decapodes.dec_mat_dual_differential(1, sd),

    # Wedge Products
    TA(∧, Sort[PrimalForm(0), PrimalForm(1)]) => Decapodes.dec_pair_wedge_product(Tuple{0,1}, sd),
    TA(∧, Sort[PrimalForm(1), PrimalForm(0)]) => Decapodes.dec_pair_wedge_product(Tuple{1,0}, sd),
    TA(∧, Sort[PrimalForm(0), PrimalForm(2)]) => Decapodes.dec_pair_wedge_product(Tuple{0,2}, sd),
    TA(∧, Sort[PrimalForm(2), PrimalForm(0)]) => Decapodes.dec_pair_wedge_product(Tuple{2,0}, sd),
    TA(∧, Sort[PrimalForm(1), PrimalForm(1)]) => Decapodes.dec_pair_wedge_product(Tuple{1,1}, sd),

    # Primal-Dual Wedge Products
    TA(∧, Sort[PrimalForm(1), DualForm(1)]) => Decapodes.dec_wedge_product_pd(Tuple{1,1}, sd),
    TA(∧, Sort[PrimalForm(0), DualForm(1)]) => Decapodes.dec_wedge_product_pd(Tuple{0,1}, sd),
    TA(∧, Sort[PrimalForm(1), DualForm(1)]) => Decapodes.dec_wedge_product_dp(Tuple{1,1}, sd),
    TA(∧, Sort[PrimalForm(1), DualForm(0)]) => Decapodes.dec_wedge_product_dp(Tuple{1,0}, sd),

    # Dual-Dual Wedge Products
    # TA(∧, Sort[DualForm(1), DualForm(1)]) => Decapodes.dec_wedge_product_dd(Tuple{1,1}, sd),
    TA(∧, Sort[DualForm(1), DualForm(0)]) => Decapodes.dec_wedge_product_dd(Tuple{1,0}, sd),
    TA(∧, Sort[DualForm(0), DualForm(1)]) => Decapodes.dec_wedge_product_dd(Tuple{0,1}, sd),

    # # Dual-Dual Interior Products
    TA(ι, Sort[DualForm(1), DualForm(1)]) => Decapodes.interior_product_dd(Tuple{1,1}, sd),
    TA(ι, Sort[DualForm(1), DualForm(2)]) => Decapodes.interior_product_dd(Tuple{1,2}, sd),

    # # Dual-Dual Lie Derivatives
    # :ℒ₁ => ℒ_dd(Tuple{1,1}, sd)

    # # Dual Laplacians
    # :Δᵈ₀ => Δᵈ(Val{0},sd)
    # :Δᵈ₁ => Δᵈ(Val{1},sd)

    # # Musical Isomorphisms
    TA(♯, Sort[PrimalForm(1)]) => Decapodes.dec_♯_p(sd), # Primal(1) -> PVField
    TA(♯, Sort[DualForm(1)]) => Decapodes.dec_♯_d(sd), # Dual(1) -> DVField

    TA(♭, Sort[DualVF()]) => Decapodes.dec_♭(sd), # DVField -> Primal(1)

    # # Averaging Operator
    # :avg₀₁ => Decapodes.dec_avg₀₁(sd)
  )
end
# TODO can we use OrderedDict to retain our nice presentation?
