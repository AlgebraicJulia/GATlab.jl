module ThDEC

using ...DEC: TypedApplication, TA, Roe, RootVar 
using ...DEC.SSAs 

using Metatheory: VecExpr
using Metatheory.EGraphs

include("signature.jl") # verify operations type-check 
include("roe_overloads.jl") # overload DEC operations to act on roe (egraphs)
include("semantics.jl") # represent operations as matrices

# include("rewriting.jl")

end
