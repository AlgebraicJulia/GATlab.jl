module StdModels
export NumR

using Reexport

include("ContextMaps.jl")
include("ContextMapMacros.jl")
include("SimpleLenses.jl")
include("LensMacros.jl")
include("FinSets.jl")
include("FinMatrices.jl")
include("SliceCategories.jl")
include("Rigs.jl")
# include("Num.jl")

@reexport using .ContextMaps
@reexport using .ContextMapMacros
@reexport using .SimpleLenses
@reexport using .LensMacros
@reexport using .FinSets
@reexport using .FinMatrices
@reexport using .SliceCategories
@reexport using .Rigs

end
