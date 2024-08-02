# ## SIGNATURE TESTS

# Addition
@test Scalar() + Scalar() == Scalar()
@test Scalar() + PrimalForm(1) == PrimalForm(1)
@test PrimalForm(2) + Scalar() == PrimalForm(2)
@test_throws SortError PrimalForm(1) + PrimalForm(2)

# Negation and Subtraction
@test -Scalar() == Scalar()
@test Scalar() - Scalar() == Scalar()

# Scalar Multiplication
@test Scalar() * Scalar() == Scalar()
@test Scalar() * PrimalForm(1) == PrimalForm(1)
@test PrimalForm(2) * Scalar() == PrimalForm(2)
@test_throws SortError PrimalForm(2) * PrimalForm(1) 

# Exterior Product
@test PrimalForm(1) ∧ PrimalForm(1) == PrimalForm(2)
@test PrimalForm(1) ∧ Scalar() == PrimalForm(1)

@test_throws SortError PrimalForm(1) ∧ DualForm(1)
@test_throws SortError PrimalForm(2) ∧ PrimalForm(1)

# Time derivative
@test ∂ₜ(Scalar()) == Scalar()
@test ∂ₜ(PrimalForm(1)) == PrimalForm(1)
@test ∂ₜ(DualForm(0)) == DualForm(0)

# Derivative
@test_throws SortError d(Scalar())
@test d(PrimalForm(1)) == PrimalForm(2)
@test d(DualForm(0)) == DualForm(1)

# Hodge star
@test_throws SortError ★(Scalar())
@test ★(PrimalForm(1)) == DualForm(1)
@test ★(DualForm(0)) == PrimalForm(2)

