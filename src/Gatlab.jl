module Gatlab
using Reexport


include("GATs.jl")
include("Visualization.jl")
include("Parse.jl")
include("Theories.jl")
include("Compactify.jl")

@reexport using .GATs
@reexport using .Visualization
@reexport using .Parse
@reexport using .Theories
@reexport using .Compactify

end # module Gatlab
