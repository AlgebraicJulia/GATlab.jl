module GATlab
using Reexport

# Util contains code that could be a separate package, but we include in gatlab
# because it's too small to refactor out.
include("util/module.jl")
include("syntax/module.jl")
include("models/module.jl")

# don't reexport these
include("stdlib/module.jl")
include("nonstdlib/module.jl")

@reexport using .Util
@reexport using .Syntax
@reexport using .Models

end # module GATlab
