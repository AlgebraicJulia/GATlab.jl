module NonStdlib

using Reexport

include("theories/module.jl")
include("models/module.jl")
include("dynamics/ResourceSharers.jl")
# include("theorymaps/module.jl")
# include("derivedmodels/module.jl")

@reexport using .NonStdTheories
@reexport using .NonStdModels
@reexport using .ResourceSharers
# @reexport using .StdTheoryMaps
# @reexport using .StdDerivedModels

end
