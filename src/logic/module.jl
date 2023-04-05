module Logic

using Reexport

include("EGraphs.jl")
include("EMatching.jl")
include("ContextMaps.jl")

@reexport using .EGraphs
@reexport using .EMatching
@reexport using .ContextMaps

end
