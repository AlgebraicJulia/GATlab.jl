module Syntax

using Reexport

include("Scopes.jl")
include("GATs.jl")
include("ExprInterop.jl")

@reexport using .Scopes
@reexport using .GATs
@reexport using .ExprInterop

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
