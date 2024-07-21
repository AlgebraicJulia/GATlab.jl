module TestSignature

using DEC

using Test

# ## SIGNATURE TESTS

# Addition
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
@test_throws SortError PrimalForm(1) ∧ Scalar() 

end
