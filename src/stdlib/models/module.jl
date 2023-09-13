module StdModels

using Reexport

include("FinSets.jl")
include("FinMatrices.jl")
include("SliceCategories.jl")
include("Op.jl")
include("Nothings.jl")
include("GATs.jl")

@reexport using .FinSets
@reexport using .FinMatrices
@reexport using .SliceCategories
@reexport using .Op
@reexport using .Nothings
@reexport using .GATs

end
