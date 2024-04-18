module Syntax

using Reexport

include("Scopes.jl")
include("ExprInterop.jl")
include("GATs.jl")
include("GATContexts.jl")
include("TheoryInterface.jl")
include("TheoryMaps.jl")
include("Rename.jl")

@reexport using .Scopes
@reexport using .ExprInterop
@reexport using .GATs
@reexport using .GATContexts
@reexport using .TheoryInterface
@reexport using .TheoryMaps
@reexport using .Rename

end
