module Logic

using Reexport

include("EGraphs.jl")
include("EMatching.jl")

@reexport using .EGraphs
@reexport using .EMatching

end
