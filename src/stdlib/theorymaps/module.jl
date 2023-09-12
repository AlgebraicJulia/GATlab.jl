module StdTheoryMaps

using Reexport

include("Maps.jl") # split into files when big enough

@reexport using .Maps

end
