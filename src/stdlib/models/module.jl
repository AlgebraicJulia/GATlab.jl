module StdModels

using Reexport

include("FinSets.jl")
include("FinMatrices.jl")
include("SliceCategories.jl")

@reexport using .FinSets
@reexport using .FinMatrices
@reexport using .SliceCategories

end
