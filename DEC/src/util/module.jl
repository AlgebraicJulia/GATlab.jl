module Util

using Reexport

include("HashColor.jl")
include("Plotting.jl")

@reexport using .HashColor
@reexport using .Plotting

end
