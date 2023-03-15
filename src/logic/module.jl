module Logic

using Reexport

include("EGraphs.jl")
include("TypeChecking.jl")

@reexport using .EGraphs

end
