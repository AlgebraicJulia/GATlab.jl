module StdTheories

using Reexport

include("Categories.jl")
include("Algebra.jl")
include("Monoidal.jl")
include("Naturals.jl")

@reexport using .Categories
@reexport using .Algebra
@reexport using .Monoidal
@reexport using .Naturals

end
