# AlgebraicJulia dependencies
using DEC
import DEC.ThDEC: ∧, Δ # conflicts with CombinatorialSpaces

# preliminary dependencies for testing
using Test
using Metatheory.EGraphs

# test the signature
include("signature.jl")

# test the roe_overloads
include("roe_overloads.jl")

# test the semantics
include("semantics.jl")

# test modeling
include("model.jl")
