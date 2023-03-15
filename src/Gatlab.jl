module Gatlab
using Reexport

# Util contains code that could be a separate package, but we include in gatlab
# because it's too small to refactor out.
include("util/module.jl")

include("syntax/module.jl")

include("logic/module.jl")

# Theories contains a "standard library" of GATs.
include("theories/module.jl")

@reexport using .Util
@reexport using .Syntax
@reexport using .Logic
@reexport using .Theories

end # module Gatlab
