module Syntax

using Reexport

include("Scopes.jl")
include("GATs.jl")
include("Presentations.jl")
include("ExprInterop.jl")
include("TheoryInterface.jl")

@reexport using .Scopes
@reexport using .GATs
@reexport using .Presentations
@reexport using .ExprInterop
@reexport using .TheoryInterface

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
