module GATlab
using Reexport

# Util contains code that could be a separate package, but we include in gatlab
# because it's too small to refactor out.
include("util/module.jl")
include("syntax/module.jl")
# include("models/module.jl")
# include("stdlib/module.jl")

@reexport using .Util
@reexport using .Syntax
# @reexport using .Models
# @reexport using .Stdlib

end # module GATlab
