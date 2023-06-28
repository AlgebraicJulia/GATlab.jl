module AugmentedTheories
export AugmentedTheory, interp_val

using ..ModelInterface
using ...Syntax

abstract type AugmentedTheory{T<:AbstractTheory, M<:Model{T}} <: AbstractTheory end

"""
Overload this for a subtype of AugmentedTheory in order to build ATrms out of raw
Julia vars
"""
interp_val(T::AugmentedTheory, v::Any) = nothing

end
