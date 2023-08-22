module Syntax

using Reexport

include("Scopes.jl")

@reexport using .Scopes

# include("Theories.jl")
# include("NestedContexts.jl")
# include("TheoryMaps.jl")
# include("Pushouts.jl")
# include("Visualization.jl")
# include("AugmentedSyntax.jl")

# @reexport using .Theories
# @reexport using .NestedContexts
# @reexport using .TheoryMaps
# @reexport using .Pushouts
# @reexport using .Visualization
# @reexport using .AugmentedSyntax

end
